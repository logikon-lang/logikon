extern crate pest;
#[macro_use]
extern crate pest_derive;

#[macro_use]
extern crate log;
extern crate env_logger;

extern crate z3;

mod z3_interface;
use z3_interface::Z3Interface;

use pest::Parser;

#[derive(Parser)]
#[grammar = "logikon.pest"]
struct IdentParser;

fn main() {
    let pairs = IdentParser::parse(Rule::contract, "declare balance public Array. declare lala public UInt. define f public (). define g public ({a} b) x :- (f (f (and a b))).").unwrap_or_else(|e| panic!("{}", e));

    // Because ident_list is silent, the iterator will contain idents
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
                Rule::contract => println!("Contract:  {}", inner_span.as_str()),
                Rule::state_var_decl => println!("StateVarDecl:   {}", inner_span.as_str()),
                Rule::logikon_type => println!("Type:   {}", inner_span.as_str()),
                Rule::visibility => println!("Visibility:   {}", inner_span.as_str()),
                Rule::identifier => println!("Identifier:   {}", inner_span.as_str()),
                Rule::function_def => println!("FunctionDefinition:   {}", inner_span.as_str()),
                _ => unreachable!()
            };
        }
    }

    let z3 = Z3Interface::new();
    z3.test();
}
