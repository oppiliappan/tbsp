/// TBSP: tree-based source processor
#[derive(argh::FromArgs)]
struct Cli {
    /// read the TBSP program source from a file
    #[argh(option, short = 'f')]
    program_file: std::path::PathBuf,

    /// set the language that the file is written in
    #[argh(option, short = 'l')]
    language: String,

    /// input file to process
    #[argh(positional)]
    file: Option<std::path::PathBuf>,
}

fn main() {
    let cli: Cli = argh::from_env();

    let program = std::fs::read_to_string(&cli.program_file).unwrap_or_else(|e| {
        eprintln!(
            "failed to read program-file from `{}`: {e}",
            cli.program_file.display()
        );
        std::process::exit(-1);
    });

    let language = match cli.language.as_str() {
        "md" => tree_sitter_md::language(),
        "typescript" => tree_sitter_typescript::language_typescript(),
        "javascript" => tree_sitter_javascript::language(),
        "python" => tree_sitter_python::language(),
        "rust" => tree_sitter_rust::language(),
        lang => {
            eprintln!("unknown language `{lang}`");
            std::process::exit(-1);
        }
    };

    let file = cli
        .file
        .map(std::fs::read_to_string)
        .unwrap_or_else(try_consume_stdin)
        .unwrap_or_else(|e| {
            eprintln!("{e}");
            std::process::exit(-1)
        });

    trawk::evaluate(&file, &program, language).unwrap_or_else(|e| {
        eprintln!("{e:?}");
        std::process::exit(-1);
    });
}

fn try_consume_stdin() -> std::io::Result<String> {
    let mut buffer = String::new();
    let mut lock = std::io::stdin().lock();

    while let Ok(n) = std::io::Read::read_to_string(&mut lock, &mut buffer) {
        if n == 0 {
            break;
        }
    }

    if buffer.is_empty() {
        Err(std::io::Error::other("empty stdin"))
    } else {
        Ok(buffer)
    }
}

// fn main() {
//     let src = r#"
// # foo1
//
// bar
//
// ## foo1.1
//
// bar baz
//
// # foo2
//
// bar baz
//
// ```
// fn main() {
// }
// ```
//
// - foo
// - bar
// - baz
//
//         "#
//     .to_owned();
//
//     let program = Program::new()
//         .from_str(
//             r#"
//     BEGIN {
//         int depth = 0;
//
//         print("<html>\n");
//         print("<body>\n");
//     }
//
//     enter section {
//         depth += 1;
//     }
//     leave section {
//         depth -= 1;
//     }
//
//     enter atx_heading {
//         print("<h");
//         print(depth);
//         print(">");
//     }
//     leave atx_heading {
//         print("</h");
//         print(depth);
//         print(">\n");
//     }
//
//     enter paragraph {
//         print("<p>");
//     }
//     leave paragraph {
//         print("</p>\n");
//     }
//
//     enter list {
//         print("<ol>");
//     }
//     leave list {
//         print("</ol>\n");
//     }
//
//     enter list_item {
//         print("<li>");
//     }
//     leave list_item {
//         print("</li>\n");
//     }
//
//     enter fenced_code_block {
//         print("<pre>");
//     }
//     leave fenced_code_block {
//         print("</pre>\n");
//     }
//
//     enter inline {
//         print(text(node));
//     }
//     enter code_fence_content {
//         print(text(node));
//     }
//
//     END {
//         print("</body>\n");
//         print("</html>\n");
//     }
//     "#,
//         )
//         .unwrap();
//
//     let mut parser = tree_sitter::Parser::new();
//     let _ = parser.set_language(&tree_sitter_md::language());
//
//     let tree = parser.parse(&src, None).unwrap();
//     let cursor = tree.walk();
//
//     let mut ctx = Context::new(tree_sitter_md::language())
//         .with_input(src)
//         .with_cursor(cursor)
//         .with_program(program)
//         .unwrap();
//
//     let _ = ctx.eval();
// }
