#[derive(Debug, Default)]
pub struct Program {
    pub stanzas: Vec<Stanza>,
}

impl Program {
    pub fn new() -> Self {
        Self {
            stanzas: Vec::new(),
        }
    }

    pub fn from_str(mut self, i: &str) -> Result<Self, nom::error::Error<&str>> {
        use nom::Finish;
        let (remaining_input, stanzas) = crate::parser::parse_file(i).finish()?;
        assert!(remaining_input.trim().is_empty(), "{remaining_input}");
        self.stanzas = stanzas;
        Ok(self)
    }

    pub fn begin(&self) -> Option<&Block> {
        self.stanzas
            .iter()
            .find(|stanza| stanza.pattern == Pattern::Begin)
            .map(|s| &s.statements)
    }

    pub fn end(&self) -> Option<&Block> {
        self.stanzas
            .iter()
            .find(|stanza| stanza.pattern == Pattern::End)
            .map(|s| &s.statements)
    }

    pub fn stanza_by_node(&self, node: tree_sitter::Node, state: Modifier) -> Option<&Block> {
        self.stanzas
            .iter()
            .find(|stanza| {
                stanza.pattern.matches(node)
                    && matches!(stanza.pattern, Pattern::Tree { modifier, .. } if modifier == state)
            })
            .map(|s| &s.statements)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Stanza {
    pub pattern: Pattern,
    pub statements: Block,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Pattern {
    Begin,
    End,
    Tree {
        modifier: Modifier,
        matcher: TreePattern,
    },
}

impl Pattern {
    pub fn matches(&self, node: tree_sitter::Node) -> bool {
        match self {
            Self::Begin | Self::End => false,
            Self::Tree { matcher, .. } => matcher.matches(node),
        }
    }
}

#[derive(Default, Debug, Eq, PartialEq, Clone, Copy)]
pub enum Modifier {
    #[default]
    Enter,
    Leave,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum TreePattern {
    Atom(String),
    List(Vec<TreePattern>),
}

impl TreePattern {
    pub fn matches(&self, node: tree_sitter::Node) -> bool {
        match self {
            Self::Atom(kind) => node.kind() == kind,
            Self::List(l) => match l.as_slice() {
                &[] => panic!(),
                [kind] => kind.matches(node),
                [root, rest @ ..] => {
                    let root_match = root.matches(node);
                    let child_match = rest
                        .iter()
                        .zip(node.named_children(&mut node.walk()))
                        .all(|(pat, child)| pat.matches(child));
                    root_match && child_match
                }
            },
        }
    }
}

#[derive(Debug, Default, Eq, PartialEq, Clone)]
pub struct Block {
    pub body: Vec<Statement>,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Statement {
    Bare(Expr),
    Declaration(Declaration),
}

impl Statement {
    #[cfg(test)]
    pub fn decl(ty: Type, ident: &str, init: Expr) -> Self {
        Self::Declaration(Declaration {
            ty,
            name: ident.to_owned(),
            init: Some(init.boxed()),
        })
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Expr {
    Node,
    Unit,
    Lit(Literal),
    Ident(Identifier),
    FieldAccess(Box<Expr>, Identifier),
    Index(Box<Expr>, Box<Expr>),
    Bin(Box<Expr>, BinOp, Box<Expr>),
    Unary(Box<Expr>, UnaryOp),
    Call(Call),
    List(List),
    If(IfExpr),
    Block(Block),
}

impl Expr {
    pub fn boxed(self) -> Box<Expr> {
        Box::new(self)
    }

    #[cfg(test)]
    pub fn bin(lhs: Expr, op: &str, rhs: Expr) -> Expr {
        use std::str::FromStr;
        Self::Bin(lhs.boxed(), BinOp::from_str(op).unwrap(), rhs.boxed())
    }

    #[cfg(test)]
    pub fn ident(i: &str) -> Expr {
        Self::Ident(i.to_owned())
    }

    #[cfg(test)]
    pub fn call<const N: usize>(fun: &str, params: [Expr; N]) -> Expr {
        Self::Call(Call {
            function: fun.to_owned(),
            parameters: params.to_vec(),
        })
    }

    #[cfg(test)]
    pub fn list<const N: usize>(items: [Expr; N]) -> Expr {
        Self::List(List {
            items: items.to_vec(),
        })
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum UnaryOp {
    Not,
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum BinOp {
    Arith(ArithOp),
    Cmp(CmpOp),
    Logic(LogicOp),
    // =
    Assign(AssignOp),
}

impl std::str::FromStr for BinOp {
    type Err = ();
    fn from_str(val: &str) -> Result<Self, Self::Err> {
        match val {
            "+" => Ok(Self::Arith(ArithOp::Add)),
            "-" => Ok(Self::Arith(ArithOp::Sub)),
            "*" => Ok(Self::Arith(ArithOp::Mul)),
            "/" => Ok(Self::Arith(ArithOp::Div)),
            "%" => Ok(Self::Arith(ArithOp::Mod)),
            ">" => Ok(Self::Cmp(CmpOp::Gt)),
            "<" => Ok(Self::Cmp(CmpOp::Lt)),
            ">=" => Ok(Self::Cmp(CmpOp::Gte)),
            "<=" => Ok(Self::Cmp(CmpOp::Lte)),
            "==" => Ok(Self::Cmp(CmpOp::Eq)),
            "!=" => Ok(Self::Cmp(CmpOp::Neq)),
            "&&" => Ok(Self::Logic(LogicOp::And)),
            "||" => Ok(Self::Logic(LogicOp::Or)),
            "=" => Ok(Self::Assign(AssignOp { op: None })),
            "+=" => Ok(Self::Assign(AssignOp {
                op: Some(ArithOp::Add),
            })),
            "-=" => Ok(Self::Assign(AssignOp {
                op: Some(ArithOp::Sub),
            })),
            "*=" => Ok(Self::Assign(AssignOp {
                op: Some(ArithOp::Mul),
            })),
            "/=" => Ok(Self::Assign(AssignOp {
                op: Some(ArithOp::Div),
            })),
            "%=" => Ok(Self::Assign(AssignOp {
                op: Some(ArithOp::Mod),
            })),
            _ => Err(()),
        }
    }
}

// + - * /
#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

// && ||
#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum LogicOp {
    And,
    Or,
}

// == != > < >= <=
#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum CmpOp {
    Eq,
    Neq,
    Gt,
    Lt,
    Gte,
    Lte,
}

// =, +=, -=, *=, /=
#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub struct AssignOp {
    pub op: Option<ArithOp>,
}

pub type Identifier = String;

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Literal {
    Str(String),
    Int(i128),
    Bool(bool),
}

/// A function call
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Call {
    pub function: Identifier,
    pub parameters: Vec<Expr>,
}

impl From<Call> for Expr {
    fn from(expr: Call) -> Expr {
        Expr::Call(expr)
    }
}

/// A list construction expression
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct List {
    pub items: Vec<Expr>,
}

impl From<List> for Expr {
    fn from(list: List) -> Expr {
        Expr::List(list)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Type {
    Unit,
    Integer,
    String,
    Boolean,
    Node,
    List,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Declaration {
    pub ty: Type,
    pub name: Identifier,
    pub init: Option<Box<Expr>>,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct IfExpr {
    pub condition: Box<Expr>,
    pub then: Block,
    pub else_: Block,
}
