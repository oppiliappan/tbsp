//! tree walking interpreter for trawk

use crate::ast;
use std::{collections::HashMap, fmt};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Variable {
    pub ty: ast::Type,
    pub name: ast::Identifier,
    pub value: Value,
}

impl Variable {
    fn value(&self) -> &Value {
        &self.value
    }

    fn ty(&self) -> ast::Type {
        self.ty
    }

    fn assign(&mut self, value: Value) -> Result {
        if self.ty() == value.ty() {
            self.value = value;
            Ok(self.value.clone())
        } else {
            Err(Error::TypeMismatch {
                expected: self.ty(),
                got: value.ty(),
            })
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Value {
    Unit,
    Integer(i128),
    String(String),
    Boolean(bool),
    Node,
    FieldAccess(Vec<String>),
}

impl Value {
    fn ty(&self) -> ast::Type {
        match self {
            Self::Unit => ast::Type::Unit,
            Self::Integer(_) => ast::Type::Integer,
            Self::String(_) => ast::Type::String,
            Self::Boolean(_) => ast::Type::Boolean,
            Self::Node => ast::Type::Node,
            Self::FieldAccess(_) => ast::Type::Node,
        }
    }

    fn default(ty: ast::Type) -> Self {
        match ty {
            ast::Type::Unit => Self::Unit,
            ast::Type::Integer => Self::default_int(),
            ast::Type::String => Self::default_string(),
            ast::Type::Boolean => Self::default_bool(),
            ast::Type::Node => unreachable!(),
        }
    }

    fn default_int() -> Self {
        Self::Integer(0)
    }

    fn default_bool() -> Self {
        Self::Boolean(false)
    }

    fn default_string() -> Self {
        Self::String(String::default())
    }

    fn as_boolean(&self) -> Option<bool> {
        match self {
            Self::Boolean(b) => Some(*b),
            _ => None,
        }
    }

    fn add(&self, other: &Self) -> Result {
        match (self, other) {
            (Self::Integer(s), Self::Integer(o)) => Ok(Self::Integer(*s + *o)),
            (Self::String(s), Self::String(o)) => Ok(Self::String(format!("{s}{o}"))),
            _ => Err(Error::UndefinedBinOp(
                ast::BinOp::Arith(ast::ArithOp::Add),
                self.ty(),
                other.ty(),
            )),
        }
    }

    fn sub(&self, other: &Self) -> Result {
        match (self, other) {
            (Self::Integer(s), Self::Integer(o)) => Ok(Self::Integer(*s - *o)),
            (Self::String(s), Self::String(o)) => {
                Ok(Self::String(s.strip_suffix(o).unwrap_or(s).to_owned()))
            }
            _ => Err(Error::UndefinedBinOp(
                ast::BinOp::Arith(ast::ArithOp::Sub),
                self.ty(),
                other.ty(),
            )),
        }
    }

    fn mul(&self, other: &Self) -> Result {
        match (self, other) {
            (Self::Integer(s), Self::Integer(o)) => Ok(Self::Integer(*s * *o)),
            _ => Err(Error::UndefinedBinOp(
                ast::BinOp::Arith(ast::ArithOp::Mul),
                self.ty(),
                other.ty(),
            )),
        }
    }

    fn div(&self, other: &Self) -> Result {
        match (self, other) {
            (Self::Integer(s), Self::Integer(o)) => Ok(Self::Integer(*s / *o)),
            _ => Err(Error::UndefinedBinOp(
                ast::BinOp::Arith(ast::ArithOp::Div),
                self.ty(),
                other.ty(),
            )),
        }
    }

    fn mod_(&self, other: &Self) -> Result {
        match (self, other) {
            (Self::Integer(s), Self::Integer(o)) => Ok(Self::Integer(*s % *o)),
            _ => Err(Error::UndefinedBinOp(
                ast::BinOp::Arith(ast::ArithOp::Mod),
                self.ty(),
                other.ty(),
            )),
        }
    }

    fn equals(&self, other: &Self) -> Result {
        match (self, other) {
            (Self::Integer(s), Self::Integer(o)) => Ok(Self::Boolean(s == o)),
            (Self::String(s), Self::String(o)) => Ok(Self::Boolean(s == o)),
            (Self::Boolean(s), Self::Boolean(o)) => Ok(Self::Boolean(s == o)),
            _ => Err(Error::UndefinedBinOp(
                ast::BinOp::Cmp(ast::CmpOp::Eq),
                self.ty(),
                other.ty(),
            )),
        }
    }

    fn greater_than(&self, other: &Self) -> Result {
        match (self, other) {
            (Self::Integer(s), Self::Integer(o)) => Ok(Self::Boolean(s > o)),
            (Self::String(s), Self::String(o)) => Ok(Self::Boolean(s.cmp(o).is_gt())),
            _ => Err(Error::UndefinedBinOp(
                ast::BinOp::Cmp(ast::CmpOp::Gt),
                self.ty(),
                other.ty(),
            )),
        }
    }

    fn less_than(&self, other: &Self) -> Result {
        match (self, other) {
            (Self::Integer(s), Self::Integer(o)) => Ok(Self::Boolean(s < o)),
            (Self::String(s), Self::String(o)) => Ok(Self::Boolean(s.cmp(o).is_lt())),
            _ => Err(Error::UndefinedBinOp(
                ast::BinOp::Cmp(ast::CmpOp::Lt),
                self.ty(),
                other.ty(),
            )),
        }
    }

    fn greater_than_equals(&self, other: &Self) -> Result {
        match (self, other) {
            (Self::Integer(s), Self::Integer(o)) => Ok(Self::Boolean(s >= o)),
            (Self::String(s), Self::String(o)) => Ok(Self::Boolean(s.cmp(o).is_ge())),
            (Self::Boolean(s), Self::Boolean(o)) => Ok(Self::Boolean(s == o)),
            _ => Err(Error::UndefinedBinOp(
                ast::BinOp::Cmp(ast::CmpOp::Gte),
                self.ty(),
                other.ty(),
            )),
        }
    }

    fn less_than_equals(&self, other: &Self) -> Result {
        match (self, other) {
            (Self::Integer(s), Self::Integer(o)) => Ok(Self::Boolean(s <= o)),
            (Self::String(s), Self::String(o)) => Ok(Self::Boolean(s.cmp(o).is_le())),
            (Self::Boolean(s), Self::Boolean(o)) => Ok(Self::Boolean(s == o)),
            _ => Err(Error::UndefinedBinOp(
                ast::BinOp::Cmp(ast::CmpOp::Lte),
                self.ty(),
                other.ty(),
            )),
        }
    }

    fn not(&self) -> Result {
        match self {
            Self::Boolean(s) => Ok(Self::Boolean(!s)),
            _ => Err(Error::UndefinedUnaryOp(ast::UnaryOp::Not, self.ty())),
        }
    }

    fn and(&self, other: &Self) -> Result {
        match (self, other) {
            (Self::Boolean(s), Self::Boolean(o)) => Ok(Self::Boolean(*s && *o)),
            _ => Err(Error::UndefinedBinOp(
                ast::BinOp::Logic(ast::LogicOp::And),
                self.ty(),
                other.ty(),
            )),
        }
    }

    fn or(&self, other: &Self) -> Result {
        match (self, other) {
            (Self::Boolean(s), Self::Boolean(o)) => Ok(Self::Boolean(*s || *o)),
            _ => Err(Error::UndefinedBinOp(
                ast::BinOp::Logic(ast::LogicOp::Or),
                self.ty(),
                other.ty(),
            )),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Integer(i) => write!(f, "{i}"),
            Self::String(s) => write!(f, "{s}"),
            Self::Boolean(b) => write!(f, "{b}"),
            Self::Node => write!(f, "<node>"),
            Self::FieldAccess(items) => write!(f, "<node>.{}", items.join(".")),
        }
    }
}

type NodeKind = u16;

#[derive(Debug, Default)]
struct Visitor {
    enter: ast::Block,
    leave: ast::Block,
}

#[derive(Debug)]
struct Visitors {
    visitors: HashMap<NodeKind, Visitor>,
    begin: ast::Block,
    end: ast::Block,
}

impl Default for Visitors {
    fn default() -> Self {
        Self::new()
    }
}

impl Visitors {
    pub fn new() -> Self {
        Self {
            visitors: HashMap::new(),
            begin: ast::Block { body: vec![] },
            end: ast::Block { body: vec![] },
        }
    }

    pub fn insert(
        &mut self,
        stanza: ast::Stanza,
        language: &tree_sitter::Language,
    ) -> std::result::Result<(), Error> {
        match &stanza.pattern {
            ast::Pattern::Begin => self.begin = stanza.statements,
            ast::Pattern::End => self.end = stanza.statements,
            ast::Pattern::Node(ast::NodePattern { modifier, kind }) => {
                let id = language.id_for_node_kind(&kind, true);
                if id == 0 {
                    return Err(Error::InvalidNodeKind(kind.to_owned()));
                }
                let v = self.visitors.entry(id).or_default();
                match modifier {
                    ast::Modifier::Enter => v.enter = stanza.statements.clone(),
                    ast::Modifier::Leave => v.leave = stanza.statements.clone(),
                };
            }
        }
        Ok(())
    }

    pub fn get_by_node(&self, node: tree_sitter::Node) -> Option<&Visitor> {
        let node_id = node.kind_id();
        self.visitors.get(&node_id)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    FailedLookup(ast::Identifier),
    TypeMismatch { expected: ast::Type, got: ast::Type },
    UndefinedBinOp(ast::BinOp, ast::Type, ast::Type),
    UndefinedUnaryOp(ast::UnaryOp, ast::Type),
    AlreadyBound(ast::Identifier),
    MalformedExpr(String),
    InvalidNodeKind(String),
    // current node is only set in visitors, not in BEGIN or END blocks
    CurrentNodeNotPresent,
}

pub type Result = std::result::Result<Value, Error>;

pub struct Context<'a> {
    variables: HashMap<ast::Identifier, Variable>,
    language: tree_sitter::Language,
    visitors: Visitors,
    input_src: Option<String>,
    cursor: Option<tree_sitter::TreeCursor<'a>>,
}

impl<'a> fmt::Debug for Context<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Context")
            .field("variables", &self.variables)
            .field("language", &self.language)
            .field("visitors", &self.visitors)
            .field("input_src", &self.input_src)
            .field(
                "cursor",
                if self.cursor.is_some() {
                    &"Some(<cursor>)"
                } else {
                    &"None"
                },
            )
            .finish()
    }
}

impl<'a> Context<'a> {
    pub fn new(language: tree_sitter::Language) -> Self {
        Self {
            visitors: Default::default(),
            variables: Default::default(),
            language,
            input_src: None,
            cursor: None,
        }
    }

    pub fn with_program(mut self, program: ast::Program) -> std::result::Result<Self, Error> {
        for stanza in program.stanzas.into_iter() {
            self.visitors.insert(stanza, &self.language)?;
        }
        Ok(self)
    }

    pub fn with_input(mut self, src: String) -> Self {
        self.input_src = Some(src);
        self
    }

    pub fn with_cursor(mut self, cursor: tree_sitter::TreeCursor<'a>) -> Self {
        self.cursor = Some(cursor);
        self
    }

    fn eval_expr(&mut self, expr: &ast::Expr) -> Result {
        match expr {
            ast::Expr::Unit => Ok(Value::Unit),
            ast::Expr::Lit(lit) => self.eval_lit(lit),
            ast::Expr::Ident(ident) => self.lookup(ident).map(Variable::value).cloned(),
            ast::Expr::Bin(lhs, op, rhs) => self.eval_bin(&*lhs, *op, &*rhs),
            ast::Expr::Unary(expr, op) => self.eval_unary(&*expr, *op),
            ast::Expr::Call(call) => self.eval_call(&*call),
            ast::Expr::IfExpr(if_expr) => self.eval_if(if_expr),
            ast::Expr::Block(block) => self.eval_block(block),
            ast::Expr::Node => Ok(Value::Node),
            ast::Expr::FieldAccess(items) => Ok(Value::FieldAccess(items.to_owned())),
        }
    }

    fn eval_lit(&mut self, lit: &ast::Literal) -> Result {
        match lit {
            ast::Literal::Str(s) => Ok(Value::String(s.to_owned())),
            ast::Literal::Int(i) => Ok(Value::Integer(*i)),
            ast::Literal::Bool(b) => Ok(Value::Boolean(*b)),
        }
    }

    fn lookup(&mut self, ident: &ast::Identifier) -> std::result::Result<&Variable, Error> {
        self.variables
            .get(ident)
            .ok_or_else(|| Error::FailedLookup(ident.to_owned()))
    }

    fn lookup_mut(&mut self, ident: &ast::Identifier) -> std::result::Result<&mut Variable, Error> {
        self.variables
            .get_mut(ident)
            .ok_or_else(|| Error::FailedLookup(ident.to_owned()))
    }

    fn bind(
        &mut self,
        ident: &ast::Identifier,
        ty: ast::Type,
    ) -> std::result::Result<&mut Variable, Error> {
        if self.lookup(ident).is_err() {
            Ok(self
                .variables
                .entry(ident.to_owned())
                .or_insert_with(|| Variable {
                    name: ident.to_owned(),
                    value: Value::default(ty),
                    ty,
                }))
        } else {
            Err(Error::AlreadyBound(ident.to_owned()))
        }
    }

    fn eval_bin(&mut self, lhs: &ast::Expr, op: ast::BinOp, rhs: &ast::Expr) -> Result {
        match op {
            ast::BinOp::Assign(op) => self.eval_assign(lhs, op, rhs),
            ast::BinOp::Arith(op) => self.eval_arith(lhs, op, rhs),
            ast::BinOp::Cmp(op) => self.eval_cmp(lhs, op, rhs),
            ast::BinOp::Logic(op) => self.eval_logic(lhs, op, rhs),
        }
    }

    fn eval_assign(
        &mut self,
        lhs: &ast::Expr,
        ast::AssignOp { op }: ast::AssignOp,
        rhs: &ast::Expr,
    ) -> Result {
        let ast::Expr::Ident(ident) = lhs else {
            return Err(Error::MalformedExpr(format!(
                "malformed assigment, lhs: {:?}",
                lhs
            )));
        };
        let value = self.eval_expr(rhs)?;
        let variable = self.lookup_mut(ident)?;
        match op {
            None => variable.assign(value),
            Some(ast::ArithOp::Add) => variable.assign(variable.value().add(&value)?),
            Some(ast::ArithOp::Sub) => variable.assign(variable.value().sub(&value)?),
            Some(ast::ArithOp::Mul) => variable.assign(variable.value().mul(&value)?),
            Some(ast::ArithOp::Div) => variable.assign(variable.value().div(&value)?),
            Some(ast::ArithOp::Mod) => variable.assign(variable.value().mod_(&value)?),
        }
    }

    fn eval_arith(&mut self, lhs: &ast::Expr, op: ast::ArithOp, rhs: &ast::Expr) -> Result {
        let l = self.eval_expr(lhs)?;
        let r = self.eval_expr(rhs)?;
        match op {
            ast::ArithOp::Add => l.add(&r),
            ast::ArithOp::Sub => l.sub(&r),
            ast::ArithOp::Mul => l.mul(&r),
            ast::ArithOp::Div => l.div(&r),
            ast::ArithOp::Mod => l.mod_(&r),
        }
    }

    fn eval_cmp(&mut self, lhs: &ast::Expr, op: ast::CmpOp, rhs: &ast::Expr) -> Result {
        let l = self.eval_expr(lhs)?;
        let r = self.eval_expr(rhs)?;

        match op {
            ast::CmpOp::Eq => l.equals(&r),
            ast::CmpOp::Gt => l.greater_than(&r),
            ast::CmpOp::Lt => l.less_than(&r),
            ast::CmpOp::Neq => l.equals(&r).and_then(|v| v.not()),
            ast::CmpOp::Gte => l.greater_than_equals(&r),
            ast::CmpOp::Lte => l.less_than_equals(&r),
        }
    }

    fn eval_logic(&mut self, lhs: &ast::Expr, op: ast::LogicOp, rhs: &ast::Expr) -> Result {
        let l = self.eval_expr(lhs)?;

        // short-circuit
        let l_value = l.as_boolean().ok_or_else(|| Error::TypeMismatch {
            expected: ast::Type::Boolean,
            got: l.ty(),
        })?;

        match op {
            ast::LogicOp::Or => {
                if l_value {
                    return Ok(l);
                } else {
                    let r = self.eval_expr(rhs)?;
                    l.or(&r)
                }
            }
            ast::LogicOp::And => {
                if !l_value {
                    return Ok(l);
                } else {
                    let r = self.eval_expr(rhs)?;
                    l.and(&r)
                }
            }
        }
    }

    fn eval_unary(&mut self, expr: &ast::Expr, op: ast::UnaryOp) -> Result {
        let val = self.eval_expr(expr)?;
        match op {
            ast::UnaryOp::Not => val.not(),
        }
    }

    fn eval_if(&mut self, if_expr: &ast::If) -> Result {
        let cond = self.eval_expr(&if_expr.condition)?;

        if cond.as_boolean().ok_or_else(|| Error::TypeMismatch {
            expected: ast::Type::Boolean,
            got: cond.ty(),
        })? {
            self.eval_block(&if_expr.then)
        } else {
            self.eval_block(&if_expr.else_)
        }
    }

    fn eval_call(&mut self, call: &ast::Call) -> Result {
        match (call.function.as_str(), call.parameters.as_slice()) {
            ("print", args) => {
                for arg in args {
                    let val = self.eval_expr(arg)?;
                    print!("{val}");
                }
                Ok(Value::Unit)
            }
            ("text", [arg]) => {
                let node = match self.eval_expr(arg)? {
                    Value::Node => self
                        .cursor
                        .as_ref()
                        .ok_or(Error::CurrentNodeNotPresent)?
                        .node(),
                    Value::FieldAccess(fields) => {
                        let mut node = self
                            .cursor
                            .as_ref()
                            .ok_or(Error::CurrentNodeNotPresent)?
                            .node();
                        for field in &fields {
                            node = node
                                .child_by_field_name(field.as_bytes())
                                .ok_or_else(|| Error::FailedLookup(field.to_owned()))?;
                        }
                        node
                    }
                    v => {
                        return Err(Error::TypeMismatch {
                            expected: ast::Type::Node,
                            got: v.ty(),
                        })
                    }
                };
                let text = node
                    .utf8_text(self.input_src.as_ref().unwrap().as_bytes())
                    .unwrap();
                Ok(Value::String(text.to_owned()))
            }
            (s, _) => Err(Error::FailedLookup(s.to_owned())),
        }
    }

    fn eval_declaration(&mut self, decl: &ast::Declaration) -> Result {
        let initial_value = match decl.init.as_ref() {
            Some(init) => Some(self.eval_expr(&*init)?),
            None => None,
        };
        let variable = self.bind(&decl.name, decl.ty)?;

        if let Some(init) = initial_value {
            variable.assign(init)?;
        }

        Ok(Value::Unit)
    }

    fn eval_statement(&mut self, stmt: &ast::Statement) -> Result {
        match stmt {
            ast::Statement::Bare(expr) => self.eval_expr(expr).map(|_| Value::Unit),
            ast::Statement::Declaration(decl) => self.eval_declaration(decl),
        }
    }

    fn eval_block(&mut self, block: &ast::Block) -> Result {
        for stmt in block.body.iter() {
            self.eval_statement(stmt)?;
        }
        Ok(Value::Unit)
    }

    pub fn eval(&mut self) -> Result {
        let visitors = std::mem::take(&mut self.visitors);
        let mut has_next = true;
        let mut postorder = Vec::new();

        // BEGIN block
        self.eval_block(&visitors.begin)?;

        while has_next {
            let current_node = self.cursor.as_mut().unwrap().node();
            postorder.push(current_node);

            let visitor = visitors.get_by_node(current_node);

            visitor.map(|v| self.eval_block(&v.enter));

            has_next = self.cursor.as_mut().unwrap().goto_first_child();

            if !has_next {
                has_next = self.cursor.as_mut().unwrap().goto_next_sibling();
                postorder
                    .pop()
                    .and_then(|n| visitors.get_by_node(n))
                    .map(|v| self.eval_block(&v.leave));
            }

            while !has_next && self.cursor.as_mut().unwrap().goto_parent() {
                has_next = self.cursor.as_mut().unwrap().goto_next_sibling();
                postorder
                    .pop()
                    .and_then(|n| visitors.get_by_node(n))
                    .map(|v| self.eval_block(&v.leave));
            }
        }

        // END block
        self.eval_block(&visitors.end)?;

        Ok(Value::Unit)
    }
}

pub fn evaluate(file: &str, program: &str, language: tree_sitter::Language) -> Result {
    let mut parser = tree_sitter::Parser::new();
    let _ = parser.set_language(language);

    let tree = parser.parse(file, None).unwrap();
    let cursor = tree.walk();

    let program = ast::Program::new().from_str(program).unwrap();
    let mut ctx = Context::new(tree_sitter_md::language())
        .with_input(file.to_owned())
        .with_cursor(cursor)
        .with_program(program)?;

    ctx.eval()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn bin() {
        let language = tree_sitter_python::language();
        let mut ctx = Context::new(language)
            .with_program(ast::Program::new())
            .unwrap();
        assert_eq!(
            ctx.eval_expr(&ast::Expr::Bin(
                ast::Expr::int(5).boxed(),
                ast::BinOp::Arith(ast::ArithOp::Add),
                ast::Expr::int(10).boxed(),
            )),
            Ok(Value::Integer(15))
        );
        assert_eq!(
            ctx.eval_expr(&ast::Expr::Bin(
                ast::Expr::int(5).boxed(),
                ast::BinOp::Cmp(ast::CmpOp::Eq),
                ast::Expr::int(10).boxed(),
            )),
            Ok(Value::Boolean(false))
        );
        assert_eq!(
            ctx.eval_expr(&ast::Expr::Bin(
                ast::Expr::int(5).boxed(),
                ast::BinOp::Cmp(ast::CmpOp::Lt),
                ast::Expr::int(10).boxed(),
            )),
            Ok(Value::Boolean(true))
        );
        assert_eq!(
            ctx.eval_expr(&ast::Expr::Bin(
                ast::Expr::Bin(
                    ast::Expr::int(5).boxed(),
                    ast::BinOp::Cmp(ast::CmpOp::Lt),
                    ast::Expr::int(10).boxed(),
                )
                .boxed(),
                ast::BinOp::Logic(ast::LogicOp::And),
                ast::Expr::false_().boxed()
            )),
            Ok(Value::Boolean(false))
        );
    }

    #[test]
    fn test_evaluate_blocks() {
        let language = tree_sitter_python::language();
        let mut ctx = Context::new(language)
            .with_program(ast::Program::new())
            .unwrap();
        assert_eq!(
            ctx.eval_block(&ast::Block {
                body: vec![
                    ast::Statement::Declaration(ast::Declaration {
                        ty: ast::Type::Integer,
                        name: "a".to_owned(),
                        init: None,
                    }),
                    ast::Statement::Bare(ast::Expr::Bin(
                        ast::Expr::Ident("a".to_owned()).boxed(),
                        ast::BinOp::Assign(ast::AssignOp {
                            op: Some(ast::ArithOp::Add)
                        }),
                        ast::Expr::int(5).boxed()
                    )),
                ]
            }),
            Ok(Value::Unit)
        );
        assert_eq!(
            ctx.lookup(&String::from("a")).unwrap().clone(),
            Variable {
                ty: ast::Type::Integer,
                name: "a".to_owned(),
                value: Value::Integer(5)
            }
        );
    }

    #[test]
    fn test_evaluate_if() {
        let language = tree_sitter_python::language();
        let mut ctx = Context::new(language)
            .with_program(ast::Program::new())
            .unwrap();
        assert_eq!(
            ctx.eval_block(&ast::Block {
                body: vec![
                    ast::Statement::Declaration(ast::Declaration {
                        ty: ast::Type::Integer,
                        name: "a".to_owned(),
                        init: Some(ast::Expr::int(1).boxed()),
                    }),
                    ast::Statement::Bare(ast::Expr::IfExpr(ast::If {
                        condition: ast::Expr::true_().boxed(),
                        then: ast::Block {
                            body: vec![ast::Statement::Bare(ast::Expr::Bin(
                                ast::Expr::Ident("a".to_owned()).boxed(),
                                ast::BinOp::Assign(ast::AssignOp {
                                    op: Some(ast::ArithOp::Add)
                                }),
                                ast::Expr::int(5).boxed()
                            ))]
                        },
                        else_: ast::Block {
                            body: vec![ast::Statement::Bare(ast::Expr::Bin(
                                ast::Expr::Ident("a".to_owned()).boxed(),
                                ast::BinOp::Assign(ast::AssignOp {
                                    op: Some(ast::ArithOp::Add)
                                }),
                                ast::Expr::int(10).boxed()
                            ))]
                        }
                    }))
                ]
            }),
            Ok(Value::Unit)
        );
        assert_eq!(
            ctx.lookup(&String::from("a")).unwrap().clone(),
            Variable {
                ty: ast::Type::Integer,
                name: "a".to_owned(),
                value: Value::Integer(6)
            }
        );
    }
}
