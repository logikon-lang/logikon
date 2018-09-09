extern crate pest;
#[macro_use]
extern crate pest_derive;
//extern crate z3;
extern crate colored;

//mod z3_interface;

use std::os::raw::c_char;

use codegen::logikon_compile;
use colored::*;

mod ast;
mod codegen;

use std::fs::File;
use std::io::prelude::*;

fn file_to_string(path: &str) -> String {
    let mut file = File::open(path).unwrap();
    let mut content = String::new();
    file.read_to_string(&mut content).unwrap();
    content
}

#[no_mangle]
pub fn compileStandard(input: *const c_char) -> *const c_char {
    // FIXME: implement Solidity's compileStandard here
    panic!(":(")
}

extern {
    fn emscripten_exit_with_live_runtime();
}

fn main() {
    unsafe {
        emscripten_exit_with_live_runtime();
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use pest::Parser;
    use z3::{Config, Context};
    use z3_interface::z3::Z3Interface;

    #[cfg(debug_assertions)]
    const _GRAMMAR: &'static str = include_str!("logikon.pest"); // relative to this file

    #[derive(Parser)]
    #[grammar = "logikon.pest"]
    struct ContractParser;

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
    fn z3() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let z3 = Z3Interface::with_context(&ctx);
        z3.test();
    }
}
