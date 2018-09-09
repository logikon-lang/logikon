extern crate pest;
#[macro_use]
extern crate pest_derive;

extern crate z3;

mod z3_interface;
use codegen::logikon_compile;
use z3::{Config, Context};
use z3_interface::Z3Interface;

mod ast;
mod codegen;

use pest::Parser;
use pest::*;
use std::fs::File;
use std::io::prelude::*;

#[cfg(debug_assertions)]
const _GRAMMAR: &'static str = include_str!("logikon.pest"); // relative to this file

#[derive(Parser)]
#[grammar = "logikon.pest"]
struct ContractParser;

fn file_to_string(path: &str) -> String {
    let mut file = File::open(path).unwrap();
    let mut content = String::new();
    file.read_to_string(&mut content).unwrap();
    content
}

fn main() {
    let source = file_to_string("./examples/hello_world.lk");

    let yul = logikon_compile(&ast::logikon_parse(&source));

    println!("Source in Logikon:");
    println!("{}", source);
    println!("\n\nGenerated Yul bytecode:");
    println!("{}", yul);
}

#[cfg(test)]
mod tests {

    use super::*;
    use pest::Parser;

    #[test]
    fn basic_syntax() {
        let source = file_to_string("./examples/syntax.lk");

        let pairs = ContractParser::parse(Rule::contract, &source).unwrap();

        for pair in pairs {
            let span = pair.clone().into_span();
            // A pair is a combination of the rule which matched and a span of input
            println!("Rule:    {:?}", pair.as_rule());
            println!("Span:    {:?}", span);
            println!("Text:    {}", span.as_str());

            // A pair can be converted to an iterator of the tokens which make it up:
            for inner_pair in pair.into_inner() {
                let inner_span = inner_pair.clone().into_span();
                match inner_pair.as_rule() {
                    Rule::state_var_decl => println!("StateVarDecl:   {}", inner_span.as_str()),
                    Rule::function_def => println!("FunctionDefinition:   {}", inner_span.as_str()),
                    _ => unreachable!(),
                };
            }
        }
    }

    #[test]
    fn visitor() {
        let source = file_to_string("./examples/syntax.lk");

        let pairs = ContractParser::parse(Rule::contract, &source).unwrap();

        // traverse and print nodes

        //enter parent
        //enter child 1
        //exit child 1
        //enter child 2
        //exit child2
        //exit parent
    }

    #[test]
    fn z3() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let z3 = Z3Interface::with_context(&ctx);
        z3.test();
    }
}
