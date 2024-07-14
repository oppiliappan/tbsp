/// tree-based source processor
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

impl Cli {
    fn program(&self) -> String {
        std::fs::read_to_string(&self.program_file).unwrap_or_else(|e| {
            eprintln!(
                "failed to read program-file from `{}`: {e}",
                self.program_file.display()
            );
            std::process::exit(-1);
        })
    }

    fn language(&self) -> tree_sitter::Language {
        match self.language.as_str() {
            "md" => tree_sitter_md::language(),
            "typescript" => tree_sitter_typescript::language_typescript(),
            "javascript" => tree_sitter_javascript::language(),
            "python" => tree_sitter_python::language(),
            "rust" => tree_sitter_rust::language(),
            lang => {
                eprintln!("unknown language `{lang}`");
                std::process::exit(-1);
            }
        }
    }

    fn file(&self) -> String {
        match self.file.as_ref() {
            Some(f) => std::fs::read_to_string(f).unwrap_or_else(|e| {
                eprintln!("failed to read input-file from `{}`: {e}", f.display());
                std::process::exit(-1);
            }),
            None => try_consume_stdin().unwrap_or_else(|e| {
                eprintln!("failed to read input-file from stdin: {e}");
                std::process::exit(-1);
            }),
        }
    }
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

fn main() {
    let cli: Cli = argh::from_env();

    tbsp::evaluate(&cli.file(), &cli.program(), cli.language()).unwrap_or_else(|e| {
        eprintln!("{e:?}");
        std::process::exit(-1);
    });
}
