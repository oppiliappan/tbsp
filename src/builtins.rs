use std::{collections::HashMap, sync::LazyLock};

use crate::{
    ast,
    eval::{Context, Error, Result, Value},
    Wrap,
};

macro_rules! builtins {
    ($($f:ident),* $(,)?) => {
        pub static BUILTINS: LazyLock<HashMap<&'static str, Box<dyn Fn(&mut Context, &[ast::Expr]) -> Result + Sync + Send>>> =
            LazyLock::new(|| {
                [
                    $((
                        stringify!($f),
                        Box::new($f) as Box<dyn Fn(&mut Context, &[ast::Expr]) -> Result + Sync + Send>,
                    )),*
                ]
                    .into_iter()
                    .collect()
            });
    }
}

builtins! {
    print,

    // string
    isupper,
    islower,
    substr,

    // node
    text,
    parent,
    children,
    kind,

    // list
    length,
    member,
    push,
    pop,
}

fn print(ctx: &mut Context, args: &[ast::Expr]) -> Result {
    for arg in args {
        let val = ctx.eval_expr(arg)?;
        print!("{val}");
    }
    Ok(Value::Unit)
}

fn isupper(ctx: &mut Context, args: &[ast::Expr]) -> Result {
    Ok(ctx
        .eval_expr(&get_args::<1>(args)?[0])?
        .as_str()?
        .chars()
        .all(|c| c.is_ascii_uppercase())
        .into())
}

fn islower(ctx: &mut Context, args: &[ast::Expr]) -> Result {
    Ok(ctx
        .eval_expr(&get_args::<1>(args)?[0])?
        .as_str()?
        .chars()
        .all(|c| c.is_ascii_lowercase())
        .into())
}

fn substr(ctx: &mut Context, args: &[ast::Expr]) -> Result {
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

fn text(ctx: &mut Context, args: &[ast::Expr]) -> Result {
    let v = ctx.eval_expr(&get_args::<1>(args)?[0])?;
    let id = v.as_node()?;
    let node = ctx.get_node_by_id(id).unwrap();
    let text = node
        .utf8_text(ctx.input_src.as_ref().unwrap().as_bytes())
        .unwrap();
    text.to_owned().wrap(Value::String).wrap(Ok)
}

fn parent(ctx: &mut Context, args: &[ast::Expr]) -> Result {
    let v = ctx.eval_expr(&get_args::<1>(args)?[0])?;
    let id = v.as_node()?;
    let node = ctx.get_node_by_id(id).unwrap();
    let parent = node.parent();
    parent
        .map(|n| Value::Node(n.id()))
        .ok_or(Error::NoParentNode(node))
}

fn children(ctx: &mut Context, args: &[ast::Expr]) -> Result {
    let v = ctx.eval_expr(&get_args::<1>(args)?[0])?;
    let id = v.as_node()?;
    let node = ctx.get_node_by_id(id).unwrap();
    let children = node
        .children(&mut node.walk())
        .map(|c| Value::Node(c.id()))
        .collect::<Vec<_>>();
    Ok(Value::List(children))
}

fn length(ctx: &mut Context, args: &[ast::Expr]) -> Result {
    let v = ctx.eval_expr(&get_args::<1>(args)?[0])?;
    let l = v.as_list()?;
    (l.len() as i128).wrap(Value::Integer).wrap(Ok)
}

fn kind(ctx: &mut Context, args: &[ast::Expr]) -> Result {
    let v = ctx.eval_expr(&get_args::<1>(args)?[0])?;
    let id = v.as_node()?;
    let node = ctx.get_node_by_id(id).unwrap();
    node.kind().to_owned().wrap(Value::String).wrap(Ok)
}

fn member(ctx: &mut Context, args: &[ast::Expr]) -> Result {
    let [list_expr, element_expr] = get_args::<2>(args)?;
    let list = ctx.eval_expr(&list_expr)?;
    let v = list.as_list()?;
    let element = ctx.eval_expr(&element_expr)?;
    v.iter()
        .any(|item| item == &element)
        .wrap(Value::Boolean)
        .wrap(Ok)
}

fn push(ctx: &mut Context, args: &[ast::Expr]) -> Result {
    let [lhs, rhs] = get_args::<2>(args)?;
    let ast::Expr::Ident(ident) = lhs else {
        return Err(Error::MalformedExpr(format!(
            "malformed assigment, lhs: {:?}",
            lhs
        )));
    };
    let element = ctx.eval_expr(&rhs)?;
    let variable = ctx.lookup_mut(ident)?;
    variable.mutate(|v| match &mut v.value {
        Value::List(l) => {
            l.push(element);
            Ok(Value::Unit)
        }
        _ => Err(Error::TypeMismatch {
            expected: ast::Type::List,
            got: v.ty().clone(),
        }),
    })
}

fn pop(ctx: &mut Context, args: &[ast::Expr]) -> Result {
    let [lhs] = get_args::<1>(args)?;
    let ast::Expr::Ident(ident) = lhs else {
        return Err(Error::MalformedExpr(format!(
            "malformed assigment, lhs: {:?}",
            lhs
        )));
    };
    let variable = ctx.lookup_mut(ident)?;
    variable.mutate(|v| match &mut v.value {
        Value::List(l) => l
            .pop()
            .ok_or_else(|| Error::ArrayOutOfBounds { idx: 0, len: 0 }),
        _ => Err(Error::TypeMismatch {
            expected: ast::Type::List,
            got: v.ty().clone(),
        }),
    })
}

fn get_args<const N: usize>(args: &[ast::Expr]) -> std::result::Result<&[ast::Expr; N], Error> {
    args.try_into().map_err(|_| Error::IncorrectArgFormat {
        wanted: N,
        got: args.len(),
    })
}
