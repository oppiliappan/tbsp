use trawk::{Context, Program};

fn main() {
    let src = r#"
bar = 0
def foo():
    baz = 5
        "#
    .to_owned();

    let program = Program::new()
        .from_str(
            r#"
    BEGIN {
        bool in_def = false;
    }
    pre function_definition {
        in_def = true;
    }
    post function_definition {
        in_def = false;
    }
    pre identifier {
        if (in_def) {
            print(text(node));
            print(" ");
            print("in def\n");
        } else {
        };
    }"#,
        )
        .unwrap();

    let mut parser = tree_sitter::Parser::new();
    let _ = parser.set_language(tree_sitter_python::language());

    let tree = parser.parse(&src, None).unwrap();
    let cursor = tree.walk();

    let mut ctx = Context::new(tree_sitter_python::language())
        .with_input(src)
        .with_cursor(cursor)
        .with_program(program)
        .unwrap();

    let _ = ctx.eval();
}
