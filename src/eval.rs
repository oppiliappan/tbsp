//! tree walking interpreter for tbsp

use crate::{ast, Wrap};
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

    fn ty(&self) -> &ast::Type {
        &self.ty
    }

    fn assign(&mut self, value: Value) -> Result {
        if self.ty() == &value.ty() {
            self.value = value;
            Ok(self.value.clone())
        } else {
            Err(Error::TypeMismatch {
                expected: self.ty().clone(),
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
    Node(NodeId),
    List(Vec<Value>),
}

type NodeId = usize;

impl Value {
    fn ty(&self) -> ast::Type {
        match self {
            Self::Unit => ast::Type::Unit,
            Self::Integer(_) => ast::Type::Integer,
            Self::String(_) => ast::Type::String,
            Self::Boolean(_) => ast::Type::Boolean,
            Self::Node(_) => ast::Type::Node,
            Self::List(_) => ast::Type::List,
        }
    }

    fn default(ty: ast::Type) -> Self {
        match ty {
            ast::Type::Unit => Self::Unit,
            ast::Type::Integer => Self::default_int(),
            ast::Type::String => Self::default_string(),
            ast::Type::Boolean => Self::default_bool(),
            ast::Type::Node => unreachable!(),
            ast::Type::List => Self::default_list(),
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

    fn default_list() -> Self {
        Self::List(Vec::new())
    }

    fn as_boolean(&self) -> std::result::Result<bool, Error> {
        match self {
            Self::Boolean(b) => Ok(*b),
            v => Err(Error::TypeMismatch {
                expected: ast::Type::Boolean,
                got: v.ty(),
            }),
        }
    }

    fn as_str(&self) -> std::result::Result<&str, Error> {
        match self {
            Self::String(s) => Ok(s.as_str()),
            v => Err(Error::TypeMismatch {
                expected: ast::Type::String,
                got: v.ty(),
            }),
        }
    }

    fn as_int(&self) -> std::result::Result<i128, Error> {
        match self {
            Self::Integer(i) => Ok(*i),
            v => Err(Error::TypeMismatch {
                expected: ast::Type::Integer,
                got: v.ty(),
            }),
        }
    }

    fn as_node(&self) -> std::result::Result<NodeId, Error> {
        match self {
            Self::Node(id) => Ok(*id),
            v => Err(Error::TypeMismatch {
                expected: ast::Type::Node,
                got: v.ty(),
            }),
        }
    }

    fn as_list(&self) -> std::result::Result<Vec<Value>, Error> {
        match self {
            Self::List(values) => Ok(values.clone()),
            v => Err(Error::TypeMismatch {
                expected: ast::Type::List,
                got: v.ty(),
            }),
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
            (Self::Integer(s), Self::String(o)) => Ok(Self::String(o.repeat(*s as usize))),
            (Self::String(_), Self::Integer(_)) => other.mul(self),
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
            Self::Node(id) => write!(f, "<node #{id}>"),
            Self::List(items) => {
                write!(f, "[")?;
                for i in items {
                    write!(f, "{i}")?;
                }
                write!(f, "]")
            }
        }
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Self::Boolean(value)
    }
}

impl From<i128> for Value {
    fn from(value: i128) -> Self {
        Self::Integer(value)
    }
}

impl From<&str> for Value {
    fn from(value: &str) -> Self {
        Self::String(value.to_owned())
    }
}

impl From<Vec<Value>> for Value {
    fn from(value: Vec<Value>) -> Self {
        Self::List(value)
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
    TypeMismatch {
        expected: ast::Type,
        got: ast::Type,
    },
    UndefinedBinOp(ast::BinOp, ast::Type, ast::Type),
    UndefinedUnaryOp(ast::UnaryOp, ast::Type),
    AlreadyBound(ast::Identifier),
    MalformedExpr(String),
    InvalidNodeKind(String),
    NoParentNode(tree_sitter::Node<'static>),
    InvalidStringSlice {
        length: usize,
        start: i128,
        end: i128,
    },
    ArrayOutOfBounds {
        idx: i128,
        len: usize
    },
    // current node is only set in visitors, not in BEGIN or END blocks
    CurrentNodeNotPresent,
}

pub type Result = std::result::Result<Value, Error>;

pub struct Context {
    variables: HashMap<ast::Identifier, Variable>,
    language: tree_sitter::Language,
    visitors: Visitors,
    input_src: Option<String>,
    cursor: Option<tree_sitter::TreeCursor<'static>>,
    tree: Option<&'static tree_sitter::Tree>,
    cache: HashMap<NodeId, tree_sitter::Node<'static>>,
}

impl fmt::Debug for Context {
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

impl Context {
    pub fn new(language: tree_sitter::Language) -> Self {
        Self {
            visitors: Default::default(),
            variables: Default::default(),
            language,
            input_src: None,
            cursor: None,
            tree: None,
            cache: HashMap::default(),
        }
    }

    pub fn cache_node(&mut self, node: tree_sitter::Node<'static>) {
        self.cache.entry(node.id()).or_insert(node);
    }

    pub fn get_node_by_id(&mut self, id: usize) -> Option<tree_sitter::Node<'static>> {
        let root_node = self.tree.as_ref().map(|t| t.root_node())?;
        self.get_node_by_id_helper(root_node, id)
    }

    fn get_node_by_id_helper(
        &mut self,
        start: tree_sitter::Node<'static>,
        id: usize,
    ) -> Option<tree_sitter::Node<'static>> {
        self.cache_node(start);

        if let Some(found) = self.cache.get(&id) {
            return Some(*found);
        }

        if start.id() == id {
            return Some(start);
        } else {
            for child in start.children(&mut start.walk()) {
                if let Some(n) = self.get_node_by_id_helper(child, id) {
                    return Some(n);
                };
            }
        }

        None
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

    pub fn with_tree(mut self, tree: tree_sitter::Tree) -> Self {
        let tree = Box::leak(Box::new(tree));
        self.cursor = Some(tree.walk());
        self.tree = Some(tree);
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
            ast::Expr::List(list) => self.eval_list(&*list),
            ast::Expr::Index(target, idx) => self.eval_index(&*target, &*idx),
            ast::Expr::If(if_expr) => self.eval_if(if_expr),
            ast::Expr::Block(block) => self.eval_block(block),
            ast::Expr::Node => self.eval_node(),
            ast::Expr::FieldAccess(expr, items) => self.eval_field_access(expr, items),
        }
    }

    fn eval_lit(&mut self, lit: &ast::Literal) -> Result {
        match lit {
            ast::Literal::Str(s) => Ok(Value::String(s.to_owned())),
            ast::Literal::Int(i) => Ok(Value::Integer(*i)),
            ast::Literal::Bool(b) => Ok(Value::Boolean(*b)),
        }
    }

    fn eval_node(&mut self) -> Result {
        self.cursor
            .as_ref()
            .ok_or(Error::CurrentNodeNotPresent)?
            .node()
            .id()
            .wrap(Value::Node)
            .wrap_ok()
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
            self.variables
                .entry(ident.to_owned())
                .or_insert_with(|| Variable {
                    name: ident.to_owned(),
                    value: Value::default(ty),
                    ty,
                })
                .wrap_ok()
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
        let l_value = l.as_boolean()?;

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

    fn eval_if(&mut self, if_expr: &ast::IfExpr) -> Result {
        let cond = self.eval_expr(&if_expr.condition)?;

        if cond.as_boolean()? {
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
            (predicate @ ("isupper" | "islower"), [arg]) => Ok(self
                .eval_expr(arg)?
                .as_str()?
                .chars()
                .all(|c| match predicate {
                    "isupper" => c.is_ascii_uppercase(),
                    "islower" => c.is_ascii_lowercase(),
                    _ => unreachable!(),
                })
                .into()),
            ("substr", [string, indices @ ..]) => {
                let v = self.eval_expr(string)?;
                let s = v.as_str()?;
                match indices {
                    [start, end] => {
                        let start = self.eval_expr(start)?.as_int()?;
                        let end = self.eval_expr(end)?.as_int()?;
                        if start < 0
                            || start >= s.len() as i128
                            || end >= s.len() as i128
                            || start > end
                        {
                            return Err(Error::InvalidStringSlice {
                                length: s.len(),
                                start,
                                end,
                            });
                        }
                        Ok(s[start as usize..end as usize].into())
                    }
                    [end] => {
                        let end = self.eval_expr(end)?.as_int()?;
                        if end >= s.len() as i128 {
                            return Err(Error::InvalidStringSlice {
                                length: s.len(),
                                start: 0,
                                end,
                            });
                        }
                        Ok(s[..end as usize].into())
                    }
                    _ => todo!(),
                }
            }
            ("text", [arg]) => {
                let v = self.eval_expr(arg)?;
                let id = v.as_node()?;
                let node = self.get_node_by_id(id).unwrap();
                let text = node
                    .utf8_text(self.input_src.as_ref().unwrap().as_bytes())
                    .unwrap();
                Ok(Value::String(text.to_owned()))
            }
            ("parent", [arg]) => {
                let v = self.eval_expr(arg)?;
                let id = v.as_node()?;
                let node = self.get_node_by_id(id).unwrap();
                let parent = node.parent();
                parent
                    .map(|n| Value::Node(n.id()))
                    .ok_or(Error::NoParentNode(node))
            }
            (s, _) => Err(Error::FailedLookup(s.to_owned())),
        }
    }

    fn eval_list(&mut self, list: &ast::List) -> Result {
        let mut vals = vec![];
        for i in &list.items {
            vals.push(self.eval_expr(i)?);
        }
        Ok(vals.into())
    }

    fn eval_index(&mut self, target: &ast::Expr, idx: &ast::Expr) -> Result {
        let mut target = self.eval_expr(target)?.as_list()?;
        let idx = self.eval_expr(idx)?.as_int()?;
        if idx < 0 || idx >= target.len() as i128 {
            Err(Error::ArrayOutOfBounds {
                idx,
                len: target.len()
            })
        } else {
            Ok(target.remove(idx as usize))
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
            ast::Statement::Bare(expr) => self.eval_expr(expr),
            ast::Statement::Declaration(decl) => self.eval_declaration(decl),
        }
    }

    fn eval_block(&mut self, block: &ast::Block) -> Result {
        for stmt in block.body.iter() {
            self.eval_statement(stmt)?;
        }
        Ok(Value::Unit)
    }

    fn eval_field_access(&mut self, expr: &ast::Expr, field: &ast::Identifier) -> Result {
        let v = self.eval_expr(expr)?;
        let base = v.as_node()?;
        let base_node = self.get_node_by_id(base).unwrap();
        base_node
            .child_by_field_name(field)
            .ok_or(Error::InvalidNodeKind(field.clone()))
            .map(|n| n.id())
            .map(Value::Node)
    }

    fn goto_first_child(&mut self) -> bool {
        self.cursor
            .as_mut()
            .map(|c| c.goto_first_child())
            .unwrap_or_default()
    }

    pub fn eval(&mut self) -> Result {
        let visitors = std::mem::take(&mut self.visitors);
        let mut has_next = true;
        let mut postorder = Vec::new();

        // BEGIN block
        self.eval_block(&visitors.begin)?;

        while has_next {
            let current_node = self.cursor.as_ref().unwrap().node();
            postorder.push(current_node);

            let visitor = visitors.get_by_node(current_node);

            if let Some(v) = visitor {
                self.eval_block(&v.enter)?;
            }

            has_next = self.goto_first_child();

            if !has_next {
                has_next = self.cursor.as_mut().unwrap().goto_next_sibling();
                if let Some(v) = postorder.pop().and_then(|n| visitors.get_by_node(n)) {
                    self.eval_block(&v.leave)?;
                }
            }

            while !has_next && self.cursor.as_mut().unwrap().goto_parent() {
                has_next = self.cursor.as_mut().unwrap().goto_next_sibling();
                if let Some(v) = postorder.pop().and_then(|n| visitors.get_by_node(n)) {
                    self.eval_block(&v.leave)?;
                }
            }
        }

        // END block
        self.eval_block(&visitors.end)?;

        Ok(Value::Unit)
    }
}

pub fn evaluate(file: &str, program: &str, language: tree_sitter::Language) -> Result {
    let mut parser = tree_sitter::Parser::new();
    let _ = parser.set_language(&language);

    let tree = parser.parse(file, None).unwrap();

    let program = ast::Program::new().from_str(program).unwrap();
    let mut ctx = Context::new(language)
        .with_input(file.to_owned())
        .with_tree(tree)
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
                    ast::Statement::Bare(ast::Expr::If(ast::IfExpr {
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

    #[test]
    fn test_substring() {
        let language = tree_sitter_python::language();
        let mut ctx = Context::new(language)
            .with_program(ast::Program::new())
            .unwrap();
        assert_eq!(
            ctx.eval_block(&ast::Block {
                body: vec![
                    ast::Statement::Declaration(ast::Declaration {
                        ty: ast::Type::String,
                        name: "a".to_owned(),
                        init: Some(ast::Expr::str("foobar").boxed()),
                    }),
                    ast::Statement::Declaration(ast::Declaration {
                        ty: ast::Type::String,
                        name: "b".to_owned(),
                        init: Some(
                            ast::Expr::Call(ast::Call {
                                function: "substr".into(),
                                parameters: vec![
                                    ast::Expr::Ident("a".to_owned()),
                                    ast::Expr::int(0),
                                    ast::Expr::int(3),
                                ]
                            })
                            .boxed()
                        ),
                    }),
                ]
            }),
            Ok(Value::Unit)
        );
        assert_eq!(
            ctx.lookup(&String::from("b")).unwrap().clone(),
            Variable {
                ty: ast::Type::String,
                name: "b".to_owned(),
                value: "foo".into()
            }
        );
    }

    #[test]
    fn test_list() {
        let language = tree_sitter_python::language();
        let mut ctx = Context::new(language)
            .with_program(ast::Program::new())
            .unwrap();
        assert_eq!(
            ctx.eval_block(&ast::Block {
                body: vec![ast::Statement::Declaration(ast::Declaration {
                    ty: ast::Type::List,
                    name: "a".to_owned(),
                    init: Some(
                        ast::Expr::List(ast::List {
                            items: vec![ast::Expr::int(5)]
                        })
                        .boxed()
                    ),
                }),]
            }),
            Ok(Value::Unit)
        );
        assert_eq!(
            ctx.lookup(&String::from("a")).unwrap().clone(),
            Variable {
                ty: ast::Type::List,
                name: "a".to_owned(),
                value: vec![5.into()].into(),
            }
        );
    }
}
