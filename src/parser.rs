use nom::{
    branch::alt,
    bytes::complete::{is_not, tag},
    character::complete::{alpha1, alphanumeric1, char, multispace0, multispace1, one_of},
    combinator::{map, opt, recognize, value},
    error::ParseError,
    multi::{fold_many0, many0, many0_count, many1, separated_list0},
    sequence::{delimited, pair, preceded, terminated, tuple},
    IResult, Parser,
};
// use tree_sitter::Query;

use crate::ast::*;
use crate::string::parse_string;

fn ws<'a, F: 'a, O, E>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O, E>
where
    F: FnMut(&'a str) -> IResult<&'a str, O, E>,
    E: ParseError<&'a str>,
{
    delimited(multispace0, inner, multispace0)
}

// TODO use this
fn _parse_comment<'a>(i: &'a str) -> IResult<&'a str, ()> {
    value((), pair(tag("//"), is_not("\n\r")))(i)
}

fn parse_unit<'a>(i: &'a str) -> IResult<&'a str, ()> {
    let open = char('(');
    let close = char(')');
    let unit = tuple((open, close));
    value((), unit)(i)
}

fn parse_bool(i: &str) -> IResult<&str, bool> {
    let t = value(true, tag("true"));
    let f = value(false, tag("false"));
    alt((t, f)).parse(i)
}

fn parse_int<'a>(i: &'a str) -> IResult<&'a str, i128> {
    map(recognize(many1(one_of("0123456789"))), |s: &str| {
        s.parse::<i128>().unwrap()
    })(i)
}

fn parse_name(i: &str) -> IResult<&str, &str> {
    recognize(pair(
        alt((alpha1, tag("_"))),
        many0_count(alt((alphanumeric1, tag("_")))),
    ))
    .parse(i)
}

fn parse_ident(i: &str) -> IResult<&str, Identifier> {
    map(parse_name, str::to_owned)(i)
}

fn parse_lit<'a>(i: &'a str) -> IResult<&'a str, Literal> {
    alt((
        map(parse_string, Literal::Str),
        map(parse_int, Literal::Int),
        map(parse_bool, Literal::Bool),
    ))
    .parse(i)
}

fn parse_cmp_op(i: &str) -> IResult<&str, CmpOp> {
    alt((
        value(CmpOp::Eq, tag("==")),
        value(CmpOp::Neq, tag("!=")),
        value(CmpOp::Gte, tag(">=")),
        value(CmpOp::Lte, tag("<=")),
        value(CmpOp::Gt, tag(">")),
        value(CmpOp::Lt, tag("<")),
    ))
    .parse(i)
}

fn parse_assign_op(i: &str) -> IResult<&str, AssignOp> {
    let parse_arith_op = alt((
        value(ArithOp::Add, char('+')),
        value(ArithOp::Sub, char('-')),
        value(ArithOp::Mul, char('*')),
        value(ArithOp::Div, char('/')),
        value(ArithOp::Mod, char('%')),
    ));
    map(tuple((opt(parse_arith_op), char('='))), |(op, _)| {
        AssignOp { op }
    })(i)
}

fn parse_op<'a, E, T>(
    op_str: &'static str,
    op: T,
) -> impl FnMut(&'a str) -> Result<(&'a str, T), nom::Err<E>>
where
    E: ParseError<&'a str>,
    T: Copy,
{
    value(op, tag(op_str))
}

fn parse_binary<'a, P1, P2, P3, E>(
    lhs: P1,
    op: P2,
    rhs: P3,
) -> impl FnMut(&'a str) -> Result<(&'a str, Expr), nom::Err<E>>
where
    P1: Parser<&'a str, Expr, E>,
    P2: Parser<&'a str, BinOp, E>,
    P3: Parser<&'a str, Expr, E>,
    E: ParseError<&'a str>,
{
    map(tuple((lhs, op, rhs)), |(l, o, r)| {
        Expr::Bin(l.boxed(), o, r.boxed())
    })
}

fn parse_assign<'a>(i: &'a str) -> IResult<&'a str, Expr> {
    let op = map(parse_assign_op, BinOp::Assign);
    let recursive = parse_binary(parse_atom, op, parse_assign);
    let base = parse_union;
    alt((recursive, base)).parse(i)
}

fn parse_union<'a>(i: &'a str) -> IResult<&'a str, Expr> {
    let op = parse_op("||", BinOp::Logic(LogicOp::Or));
    let recursive = parse_binary(parse_intersection, op, parse_union);
    let base = parse_intersection;
    alt((recursive, base)).parse(i)
}

fn parse_intersection<'a>(i: &'a str) -> IResult<&'a str, Expr> {
    let op = parse_op("&&", BinOp::Logic(LogicOp::And));
    let recursive = parse_binary(parse_negated, op, parse_intersection);
    let base = parse_negated;
    alt((recursive, base)).parse(i)
}

fn parse_negated<'a>(i: &'a str) -> IResult<&'a str, Expr> {
    let op = parse_op("!", UnaryOp::Not);
    let recursive = map(tuple((op, parse_rel)), |(op, expr)| {
        Expr::Unary(expr.boxed(), op)
    });
    let base = parse_rel;
    alt((recursive, base)).parse(i)
}

fn parse_rel<'a>(i: &'a str) -> IResult<&'a str, Expr> {
    let op = map(parse_cmp_op, BinOp::Cmp);
    let recursive = parse_binary(parse_sum, op, parse_rel);
    let base = parse_sum;
    alt((recursive, base)).parse(i)
}

fn parse_sum<'a>(i: &'a str) -> IResult<&'a str, Expr> {
    let add = parse_op("+", BinOp::Arith(ArithOp::Add));
    let sub = parse_op("-", BinOp::Arith(ArithOp::Sub));
    let op = alt((add, sub));
    let recursive = parse_binary(parse_mul, op, parse_sum);
    let base = parse_mul;
    alt((recursive, base)).parse(i)
}

fn parse_mul<'a>(i: &'a str) -> IResult<&'a str, Expr> {
    let mul = parse_op("*", BinOp::Arith(ArithOp::Mul));
    let div = parse_op("/", BinOp::Arith(ArithOp::Div));
    let mod_ = parse_op("%", BinOp::Arith(ArithOp::Mod));
    let op = alt((mul, div, mod_));
    let recursive = parse_binary(parse_field_access, op, parse_mul);
    let base = parse_field_access;
    alt((recursive, base)).parse(i)
}

fn parse_field_access<'a>(i: &'a str) -> IResult<&'a str, Expr> {
    let trailing = map(tuple((ws(char('.')), ws(parse_ident))), |(_, i)| i);
    let (i, base) = parse_atom(i)?;

    fold_many0(
        trailing,
        move || base.clone(),
        move |acc, new| Expr::FieldAccess(acc.boxed(), new),
    )(i)
}

fn parse_atom<'a>(i: &'a str) -> IResult<&'a str, Expr> {
    let inner = alt((
        map(tag("node"), |_| Expr::Node),
        map(parse_block, Expr::Block),
        map(parse_if, Expr::If),
        map(parse_call, Expr::Call),
        map(parse_lit, Expr::Lit),
        map(parse_ident, Expr::Ident),
        map(parse_unit, |_| Expr::Unit),
    ));
    ws(inner).parse(i)
}

fn parse_call<'a>(i: &'a str) -> IResult<&'a str, Call> {
    let ident = parse_ident;
    let open = ws(char('('));
    let args = separated_list0(char(','), parse_expr);
    let close = ws(char(')'));
    map(
        tuple((ident, open, args, close)),
        |(function, _, parameters, _)| Call {
            function,
            parameters,
        },
    )
    .parse(i)
}

fn parse_block<'a>(i: &'a str) -> IResult<&'a str, Block> {
    let open = ws(char('{'));
    let statements = map(many0(parse_statement), |body| Block { body });
    let close = ws(char('}'));
    delimited(open, statements, close).parse(i)
}

fn parse_if<'a>(i: &'a str) -> IResult<&'a str, IfExpr> {
    let if_ = delimited(multispace0, tag("if"), multispace1);

    let open = char('(');
    let condition = ws(parse_expr);
    let close = terminated(char(')'), multispace0);

    let then = parse_block;

    let else_kw = ws(tag("else"));
    let else_ = opt(preceded(else_kw, parse_block));

    map(
        tuple((if_, open, condition, close, then, else_)),
        |(_, _, condition, _, then, else_)| IfExpr {
            condition: condition.boxed(),
            then,
            else_: else_.unwrap_or_default(),
        },
    )(i)
}

fn parse_expr<'a>(i: &'a str) -> IResult<&'a str, Expr> {
    parse_assign.parse(i)
}

fn parse_bare<'a>(i: &'a str) -> IResult<&'a str, Expr> {
    parse_expr(i)
}

fn parse_type<'a>(i: &'a str) -> IResult<&'a str, Type> {
    let int = value(Type::Integer, tag("int"));
    let string = value(Type::String, tag("string"));
    let bool_ = value(Type::Boolean, tag("bool"));
    alt((int, string, bool_)).parse(i)
}

fn parse_declaration<'a>(i: &'a str) -> IResult<&'a str, Declaration> {
    let ty = parse_type;
    let name = parse_ident;
    let op = ws(char('='));
    let init = opt(preceded(op, map(parse_expr, Expr::boxed)));
    map(
        tuple((ty, multispace0, name, init)),
        |(ty, _, name, init)| Declaration { ty, name, init },
    )(i)
}

fn parse_statement<'a>(i: &'a str) -> IResult<&'a str, Statement> {
    let semicolon = ws(char(';'));
    let inner = alt((
        map(parse_declaration, Statement::Declaration),
        map(parse_bare, Statement::Bare),
    ));
    terminated(inner, semicolon).parse(i)
}

// pub fn skip_query(mut i: &str) -> IResult<&str, ()> {
//     let mut paren_depth = 0;
//     let mut in_string = false;
//     let mut in_escape = false;
//     let mut in_comment = false;
//     loop {
//         let ch = i
//             .chars()
//             .next()
//             .ok_or(nom::Err::Error(nom::error::Error::new(
//                 i,
//                 nom::error::ErrorKind::Eof,
//             )))?;
//         if in_escape {
//             in_escape = false;
//         } else if in_string {
//             match ch {
//                 '\\' => {
//                     in_escape = true;
//                 }
//                 '"' | '\n' => {
//                     in_string = false;
//                 }
//                 _ => {}
//             }
//         } else if in_comment {
//             if ch == '\n' {
//                 in_comment = false;
//             }
//         } else {
//             match ch {
//                 '"' => in_string = true,
//                 '(' => paren_depth += 1,
//                 ')' => {
//                     if paren_depth > 0 {
//                         paren_depth -= 1;
//                     }
//                 }
//                 '{' => return Ok((i, ())),
//                 ';' => in_comment = true,
//                 _ => {}
//             }
//         }
//         i = &i[1..];
//     }
// }

// fn parse_query<'a>(
//     language: tree_sitter::Language,
// ) -> impl FnMut(&'a str) -> IResult<&'a str, Query> {
//     return move |initial: &'a str| {
//         let query_start = 0;
//         let (skipped, _) = skip_query(initial)?;
//         let query_end = initial.len() - skipped.len();
//         let query_source = &initial[query_start..query_end].to_owned();
//
//         let query = Query::new(language, &query_source).map_err(|mut _e| {
//             nom::Err::Error(nom::error::Error::new(initial, nom::error::ErrorKind::Fail))
//         })?;
//         Ok((skipped, query))
//     };
// }

fn parse_modifier<'a>(i: &str) -> IResult<&str, Modifier> {
    let pre = value(Modifier::Enter, tag("enter"));
    let post = value(Modifier::Leave, tag("leave"));
    map(opt(alt((pre, post))), Option::unwrap_or_default)(i)
}

fn parse_pattern<'a>(i: &str) -> IResult<&str, Pattern> {
    let begin = value(Pattern::Begin, ws(tag("BEGIN")));
    let end = value(Pattern::End, ws(tag("END")));
    let node = map(
        tuple((parse_modifier, multispace0, parse_ident)),
        |(modifier, _, kind)| Pattern::Node(NodePattern { modifier, kind }),
    );
    ws(alt((begin, end, node))).parse(i)
}

pub fn parse_stanza<'a>(i: &str) -> IResult<&str, Stanza> {
    map(
        tuple((parse_pattern, parse_block)),
        |(pattern, statements)| Stanza {
            pattern,
            statements,
        },
    )(i)
}

pub fn parse_file(i: &str) -> IResult<&str, Vec<Stanza>> {
    many0(parse_stanza).parse(i)
}

#[cfg(test)]
mod test {
    use super::*;

    // test helpers
    impl Expr {
        pub fn int(int: i128) -> Expr {
            Self::Lit(Literal::Int(int))
        }

        pub fn str(s: &str) -> Expr {
            Self::Lit(Literal::Str(s.to_owned()))
        }

        pub const fn false_() -> Expr {
            Self::Lit(Literal::Bool(false))
        }

        pub const fn true_() -> Expr {
            Self::Lit(Literal::Bool(true))
        }
    }

    #[test]
    fn test_parse_unit() {
        assert_eq!(parse_unit("()"), Ok(("", ())))
    }

    #[test]
    fn test_parse_int() {
        assert_eq!(parse_int("123456"), Ok(("", 123456)));
        assert_eq!(parse_int("00123456"), Ok(("", 123456)));
    }

    #[test]
    fn test_parse_bool() {
        assert_eq!(parse_bool("true"), Ok(("", true)));
        assert_eq!(parse_bool("false"), Ok(("", false)));
    }

    #[test]
    fn test_parse_name() {
        assert_eq!(parse_name("true"), Ok(("", "true")));
        assert_eq!(parse_name("_abc"), Ok(("", "_abc")));
    }

    #[test]
    fn test_parse_literal() {
        assert_eq!(
            parse_lit(r#""foobarbaz""#),
            Ok(("", Literal::Str("foobarbaz".to_owned())))
        );
        assert_eq!(parse_lit("123"), Ok(("", Literal::Int(123))));
        assert_eq!(parse_lit("true"), Ok(("", Literal::Bool(true))));
    }

    #[test]
    fn test_parse_expr() {
        assert_eq!(parse_expr(" ()  "), Ok(("", Expr::Unit)));
        assert_eq!(parse_expr(" 55  "), Ok(("", Expr::int(55))));
        assert_eq!(
            parse_expr(" true || true  "),
            Ok((
                "",
                Expr::Bin(
                    Expr::true_().boxed(),
                    BinOp::Logic(LogicOp::Or),
                    Expr::true_().boxed()
                )
            ))
        );
        assert_eq!(
            parse_expr("true || false && 5 == 5  "),
            Ok((
                "",
                Expr::Bin(
                    Expr::true_().boxed(),
                    BinOp::Logic(LogicOp::Or),
                    Expr::Bin(
                        Expr::false_().boxed(),
                        BinOp::Logic(LogicOp::And),
                        Expr::Bin(
                            Expr::int(5).boxed(),
                            BinOp::Cmp(CmpOp::Eq),
                            Expr::int(5).boxed(),
                        )
                        .boxed()
                    )
                    .boxed()
                )
            ))
        );
        assert_eq!(
            parse_expr(" foo ( 1, 2,3 , 1 == 1)"),
            Ok((
                "",
                Expr::Call(Call {
                    function: "foo".to_owned(),
                    parameters: vec![
                        Expr::int(1),
                        Expr::int(2),
                        Expr::int(3),
                        Expr::Bin(
                            Expr::int(1).boxed(),
                            BinOp::Cmp(CmpOp::Eq),
                            Expr::int(1).boxed()
                        )
                    ],
                })
            ))
        );
        assert_eq!(
            parse_expr("a = b"),
            Ok((
                "",
                Expr::Bin(
                    Expr::Ident("a".to_owned()).boxed(),
                    BinOp::Assign(AssignOp { op: None }),
                    Expr::Ident("b".to_owned()).boxed(),
                )
            ))
        );
        assert_eq!(
            parse_expr(" a += 4 + 5"),
            Ok((
                "",
                Expr::Bin(
                    Expr::Ident("a".to_owned()).boxed(),
                    BinOp::Assign(AssignOp {
                        op: Some(ArithOp::Add)
                    }),
                    Expr::Bin(
                        Expr::int(4).boxed(),
                        BinOp::Arith(ArithOp::Add),
                        Expr::int(5).boxed(),
                    )
                    .boxed()
                )
            ))
        );
    }

    #[test]
    fn test_parse_statement() {
        assert_eq!(
            parse_statement("true;"),
            Ok(("", Statement::Bare(Expr::true_())))
        );
        assert_eq!(
            parse_statement("true ; "),
            Ok(("", Statement::Bare(Expr::true_())))
        );
        assert_eq!(
            parse_statement("int a ; "),
            Ok((
                "",
                Statement::Declaration(Declaration {
                    ty: Type::Integer,
                    name: "a".to_owned(),
                    init: None
                })
            ))
        );
        assert_eq!(
            parse_statement("int a =5 ; "),
            Ok((
                "",
                Statement::Declaration(Declaration {
                    ty: Type::Integer,
                    name: "a".to_owned(),
                    init: Some(Expr::int(5).boxed())
                })
            ))
        );
    }

    #[test]
    fn test_parse_block() {
        assert_eq!(
            parse_expr(
                r#"
            {
                true;
                1;
            }
                "#
            ),
            Ok((
                "",
                Expr::Block(Block {
                    body: vec![
                        Statement::Bare(Expr::true_()),
                        Statement::Bare(Expr::int(1)),
                    ]
                })
            ))
        );
    }

    #[test]
    fn test_parse_node() {
        assert_eq!(parse_expr(r#" node "#), Ok(("", Expr::Node)));
        assert_eq!(
            parse_expr(r#" node.foo "#),
            Ok(("", Expr::FieldAccess(Expr::Node.boxed(), "foo".to_owned())))
        );
        assert_eq!(
            parse_expr(
                r#" node
                .foo
                .bar"#
            ),
            Ok((
                "",
                Expr::FieldAccess(
                    Expr::FieldAccess(Expr::Node.boxed(), "foo".to_owned()).boxed(),
                    "bar".to_owned()
                )
            ))
        );
    }

    #[test]
    fn test_parse_if() {
        assert_eq!(
            parse_expr(
                r#"
            if (1 == true) {
                5;
            } else {
                10;
            }
                "#
            ),
            Ok((
                "",
                Expr::If(IfExpr {
                    condition: Expr::Bin(
                        Expr::int(1).boxed(),
                        BinOp::Cmp(CmpOp::Eq),
                        Expr::true_().boxed()
                    )
                    .boxed(),
                    then: Block {
                        body: vec![Statement::Bare(Expr::int(5)),]
                    },
                    else_: Block {
                        body: vec![Statement::Bare(Expr::int(10)),]
                    }
                })
            ))
        );
    }

    // #[test]
    // fn test_skip_query() {
    //     assert_eq!(
    //         skip_query(
    //             r#"(heading
    //             (paragraph) @foo) {}"#
    //         ),
    //         Ok(("{}", ()))
    //     );
    // }

    #[test]
    fn test_parse_pattern() {
        assert_eq!(
            parse_pattern("enter function_definition"),
            Ok((
                "",
                Pattern::Node(NodePattern {
                    modifier: Modifier::Enter,
                    kind: "function_definition".to_owned()
                })
            ))
        );
        assert_eq!(
            parse_pattern("function_definition"),
            Ok((
                "",
                Pattern::Node(NodePattern {
                    modifier: Modifier::Enter,
                    kind: "function_definition".to_owned()
                })
            ))
        );
        assert_eq!(
            parse_pattern("leave function_definition"),
            Ok((
                "",
                Pattern::Node(NodePattern {
                    modifier: Modifier::Leave,
                    kind: "function_definition".to_owned()
                })
            ))
        );
    }

    #[test]
    fn test_parse_stanza() {
        assert_eq!(
            parse_stanza("enter function_definition { true; }"),
            Ok((
                "",
                Stanza {
                    pattern: Pattern::Node(NodePattern {
                        modifier: Modifier::Enter,
                        kind: "function_definition".to_owned()
                    }),
                    statements: Block {
                        body: vec![Statement::Bare(Expr::true_())]
                    }
                }
            ))
        );
        assert_eq!(
            parse_stanza("BEGIN { true; }"),
            Ok((
                "",
                Stanza {
                    pattern: Pattern::Begin,
                    statements: Block {
                        body: vec![Statement::Bare(Expr::true_())]
                    }
                }
            ))
        );
        assert_eq!(
            parse_block(
                " { 
                    true;
                }"
            ),
            Ok((
                "",
                Block {
                    body: vec![Statement::Bare(Expr::true_())]
                }
            ))
        );
    }

    #[test]
    fn test_parse_if_statement_regression() {
        assert_eq!(
            parse_statement("if (true) { true; };"),
            Ok((
                "",
                Statement::Bare(Expr::If(IfExpr {
                    condition: Expr::true_().boxed(),
                    then: Block {
                        body: vec![Statement::Bare(Expr::true_())]
                    },
                    else_: Block::default(),
                }))
            ))
        );
        assert_eq!(
            parse_expr("if (true) { true; } else { true; }"),
            Ok((
                "",
                Expr::If(IfExpr {
                    condition: Expr::true_().boxed(),
                    then: Block {
                        body: vec![Statement::Bare(Expr::true_())]
                    },
                    else_: Block {
                        body: vec![Statement::Bare(Expr::true_())]
                    },
                })
            ))
        );
    }
}
