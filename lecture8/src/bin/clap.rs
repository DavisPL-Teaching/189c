/*
    Demo 3: Building command line tools with Clap

    (i.e. CLIs -- Command Line Interfaces)
*/

use clap::Parser;

#[derive(Debug, Parser)]
#[command(name = "CIS198 CLI", about = "A simple CLI example in Rust.")]
struct GreetingCLI {
    /// Name(s) of the people to greet
    #[arg(short, long, num_args = 1.., required = true)]
    names: Vec<String>,

    /// Greeting to use
    #[arg(short, long, default_value = "Hello")]
    greeting: String,

    /// Whether to print debugging information
    #[arg(short, long)]
    debug: bool,
}

fn main() {
    let args = GreetingCLI::parse();
    for name in &args.names {
        println!("{}, {}!", args.greeting, name);
    }
    if args.debug {
        dbg!(args);
    }
}
