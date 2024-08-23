#[derive(Debug)]
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
    Node(NodePattern),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct NodePattern {
    pub modifier: Modifier,
    pub kind: String,
}

#[derive(Default, Debug, Eq, PartialEq, Clone, Copy)]
pub enum Modifier {
    #[default]
    Enter,
    Leave,
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

    pub fn as_ident(self) -> Option<Identifier> {
        match self {
            Self::Ident(i) => Some(i),
            _ => None,
        }
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
