use std::{collections::HashMap, sync::LazyLock};

use crate::{
    ast,
    eval::{Context, Error, Result, Value},
    Wrap
};

pub static BUILTINS: LazyLock<HashMap<&'static str, Box<dyn Builtin + Sync + Send>>> =
    LazyLock::new(|| {
        [
            Print.boxed(),
            IsUpper.boxed(),
            IsLower.boxed(),
            Substr.boxed(),
            Text.boxed(),
            Parent.boxed(),
            Children.boxed(),
            Length.boxed(),
            Kind.boxed(),
        ]
        .into_iter()
        .map(|b| (b.id(), b))
        .collect()
    });

pub(crate) trait Builtin
where
    Self: 'static,
{
    /// Name of this function
    fn id(&self) -> &'static str;

    /// Function description
    fn eval(&self, ctx: &mut Context, args: &[ast::Expr]) -> Result;

    /// Anything that is Builtin can be turned into a trait object
    fn boxed(self) -> Box<dyn Builtin + Sync + Send>
    where
        Self: Sized + Sync + Send,
    {
        Box::new(self) as Box<dyn Builtin + Sync + Send>
    }
}

fn get_args<const N: usize>(args: &[ast::Expr]) -> std::result::Result<&[ast::Expr; N], Error> {
    args.try_into().map_err(|_| Error::IncorrectArgFormat {
        wanted: N,
        got: args.len(),
    })
}

struct Print;
impl Builtin for Print {
    fn id(&self) -> &'static str {
        "print"
    }

    fn eval(&self, ctx: &mut Context, args: &[ast::Expr]) -> Result {
        for arg in args {
            let val = ctx.eval_expr(arg)?;
            print!("{val}");
        }
        Ok(Value::Unit)
    }
}

struct IsUpper;
impl Builtin for IsUpper {
    fn id(&self) -> &'static str {
        "isupper"
    }

    fn eval(&self, ctx: &mut Context, args: &[ast::Expr]) -> Result {
        Ok(ctx
            .eval_expr(&get_args::<1>(args)?[0])?
            .as_str()?
            .chars()
            .all(|c| c.is_ascii_uppercase())
            .into())
    }
}

struct IsLower;
impl Builtin for IsLower {
    fn id(&self) -> &'static str {
        "islower"
    }

    fn eval(&self, ctx: &mut Context, args: &[ast::Expr]) -> Result {
        Ok(ctx
            .eval_expr(&get_args::<1>(args)?[0])?
            .as_str()?
            .chars()
            .all(|c| c.is_ascii_lowercase())
            .into())
    }
}

struct Substr;
impl Builtin for Substr {
    fn id(&self) -> &'static str {
        "substr"
    }

    fn eval(&self, ctx: &mut Context, args: &[ast::Expr]) -> Result {
        if let Ok([string, start, end]) = get_args::<3>(args) {
            let v = ctx.eval_expr(string)?;
            let s = v.as_str()?;
            let start = ctx.eval_expr(start)?.as_int()?;
            let end = ctx.eval_expr(end)?.as_int()?;
            if start < 0 || start >= s.len() as i128 || end >= s.len() as i128 || start > end {
                return Err(Error::InvalidStringSlice {
                    length: s.len(),
                    start,
                    end,
                });
            }
            Ok(s[start as usize..end as usize].into())
        } else {
            let [string, end] = get_args::<2>(args)?;
            let v = ctx.eval_expr(string)?;
            let s = v.as_str()?;
            let end = ctx.eval_expr(end)?.as_int()?;
            if end >= s.len() as i128 {
                return Err(Error::InvalidStringSlice {
                    length: s.len(),
                    start: 0,
                    end,
                });
            }
            Ok(s[..end as usize].into())
        }
    }
}

struct Text;
impl Builtin for Text {
    fn id(&self) -> &'static str {
        "text"
    }

    fn eval(&self, ctx: &mut Context, args: &[ast::Expr]) -> Result {
        let v = ctx.eval_expr(&get_args::<1>(args)?[0])?;
        let id = v.as_node()?;
        let node = ctx.get_node_by_id(id).unwrap();
        let text = node
            .utf8_text(ctx.input_src.as_ref().unwrap().as_bytes())
            .unwrap();
        text.to_owned().wrap(Value::String).wrap(Ok)
    }
}

struct Parent;
impl Builtin for Parent {
    fn id(&self) -> &'static str {
        "parent"
    }

    fn eval(&self, ctx: &mut Context, args: &[ast::Expr]) -> Result {
        let v = ctx.eval_expr(&get_args::<1>(args)?[0])?;
        let id = v.as_node()?;
        let node = ctx.get_node_by_id(id).unwrap();
        let parent = node.parent();
        parent
            .map(|n| Value::Node(n.id()))
            .ok_or(Error::NoParentNode(node))
    }
}

struct Children;
impl Builtin for Children {
    fn id(&self) -> &'static str {
        "children"
    }

    fn eval(&self, ctx: &mut Context, args: &[ast::Expr]) -> Result {
        let v = ctx.eval_expr(&get_args::<1>(args)?[0])?;
        let id = v.as_node()?;
        let node = ctx.get_node_by_id(id).unwrap();
        let children = node
            .children(&mut node.walk())
            .map(|c| Value::Node(c.id()))
            .collect::<Vec<_>>();
        Ok(Value::List(children))
    }
}

struct Length;
impl Builtin for Length {
    fn id(&self) -> &'static str {
        "length"
    }

    fn eval(&self, ctx: &mut Context, args: &[ast::Expr]) -> Result {
        let v = ctx.eval_expr(&get_args::<1>(args)?[0])?;
        let l = v.as_list()?;
        (l.len() as i128).wrap(Value::Integer).wrap(Ok)
    }
}

struct Kind;
impl Builtin for Kind {
    fn id(&self) -> &'static str {
        "kind"
    }

    fn eval(&self, ctx: &mut Context, args: &[ast::Expr]) -> Result {
        let v = ctx.eval_expr(&get_args::<1>(args)?[0])?;
        let id = v.as_node()?;
        let node = ctx.get_node_by_id(id).unwrap();
        node.kind().to_owned().wrap(Value::String).wrap(Ok)
    }
}
