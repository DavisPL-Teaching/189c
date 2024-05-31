/*
    Demo: Building command line tools with Clap
*/
use clap::Parser;

#[derive(Debug, Parser)]
#[command(name = "CIS198 CLI", about = "A simple CLI example in Rust.")]
struct CLI {
    /// Greeting to use
    #[arg(short, long, default_value = "Hello")]
    greeting: String,

    /// Name(s) of the people to greet
    #[arg(short, long, required = true)]
    names: Vec<String>,

    /// Whether to print debugging information
    #[arg(short, long)]
    debug: bool,
}

fn main() {
    let args = CLI::parse();
    for name in &args.names {
        println!("{}, {}!", args.greeting, name);
    }
    if args.debug {
        dbg!(args);
    }
}
