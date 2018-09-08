#[derive(Hash, PartialEq, Debug)]
struct Contract {
    state: Vec<StateVariable>,
    functions: Vec<Function>,
}

#[derive(Hash, PartialEq, Debug)]
struct StateVariable {
    name: String,
    _type: Type,
}

#[derive(Hash, PartialEq, Debug)]
struct Function {
    name: String,
    cases: Vec<Case>,
    recursive: bool,
    signature: Signature,
}

#[derive(Hash, PartialEq, Debug)]
struct Case {
    parameters: Vec<Variable>, // TODO implement patterns
    expressions: Vec<BooleanExpression>,
    return_values: Vec<Variable>,
}

#[derive(Hash, PartialEq, Debug)]
enum BooleanExpression {
    Identifier(String),

    Eq(Box<Expression>, Box<Expression>),
    Lt(Box<UintExpression>, Box<UintExpression>),
    Gt(Box<UintExpression>, Box<UintExpression>),
    Le(Box<UintExpression>, Box<UintExpression>),
    Ge(Box<UintExpression>, Box<UintExpression>),
    Ne(Box<Expression>, Box<Expression>),

    FunctionCall(String, Vec<Expression>),
}

#[derive(Hash, PartialEq, Debug)]
enum Expression {
    Boolean(BooleanExpression),
    Uint(UintExpression),
}

#[derive(Hash, PartialEq, Debug)]
enum UintExpression {
    Identifier(String),

    Select(Box<ArrayExpression>, Box<UintExpression>),
}

#[derive(Hash, PartialEq, Debug)]
enum ArrayExpression {
    Identifier(String),
    Store(Box<ArrayExpression>, UintExpression, UintExpression),
}

#[derive(Hash, PartialEq, Debug)]
struct Variable {
    name: String,
    _type: Type,
}

#[derive(Hash, PartialEq, Debug)]
enum Type {
    Uint,
    Array,
    Bool,
    List,
}

#[derive(Hash, PartialEq, Debug)]
struct Signature {
    inputs: Vec<Type>,
    outputs: Vec<Type>,
}

// impl<'a> From<Pair<'a, Rule>> for Parameter {
// 	fn from(pair: Pair<Rule>) -> Function {
// 		let mut name = String::new();
// 		let mut _type = Type::Bool;

// 		for p in pair.into_inner() {
// 			match p.as_rule() {
// 				Rule::identifier => {
// 					name = p.as_str().to_string();
// 				},

// 				c => panic!("{:?}", c)
// 			}
// 		}
// 	}
// }

impl<'a> From<Pair<'a, Rule>> for Type {
    fn from(pair: Pair<Rule>) -> Type {
        let mut t = Type::Uint;
        for p in pair.into_inner() {
            match p.as_rule() {
                Rule::logikon_type => {
                    t = match p.as_str() {
                        "Uint" => Type::Uint,
                        "Bool" => Type::Bool,
                        "List" => Type::List,
                        "Array" => Type::Array,
                        _ => panic!("die")
                    }
                },
                _ => panic!("not a type")
            }
        }
        t
    }
}

impl<'a> From<Pair<'a, Rule>> for Function {
    fn from(pair: Pair<Rule>) -> Function {
        let mut name = String::new();
        let mut cases: Vec<Case> = vec![];
        let mut recursive = false;
        let mut inputs = vec![];
        let mut outputs = vec![];

        let mut parsed_input_types = false;


        for p in pair.into_inner() {
        	match p.as_rule() {
        		Rule::identifier => {
        			name = p.as_str().to_string();
        		},
        		Rule::case => {
        			cases.push(Case::from(p));
        		},
                Rule::recursive => {
                    recursive = true;
                },
                Rule::type_list => {
                    if parsed_input_types {
                        for t in p.into_inner() {
                            outputs.push(Type::from(t))
                        }
                    } else {
                        for t in p.into_inner() {
                            inputs.push(Type::from(t))
                        }
                        parsed_input_types = true;
                    }
                }
        		c => panic!("{:?}", c)
        	}
        }

        Function {
            name,
            recursive,
            cases,
            signature: Signature {
                inputs,
                outputs,
            },
        }
    }
}

impl<'a> From<Pair<'a, Rule>> for Case {
    fn from(pair: Pair<Rule>) -> Case {
        Case {
            parameters: vec![],
            expressions: vec![],
            return_values: vec![],
        }
    }
}

use pest::iterators::Pair;
use pest::Parser;

#[cfg(debug_assertions)]
const _GRAMMAR: &'static str = include_str!("logikon.pest"); // relative to this file

#[derive(Parser)]
#[grammar = "logikon.pest"]
struct ContractParser;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_function() {
        let source = r#"define f (Uint) -> (Uint Uint) 
		case () ().
	"#;

        let mut pairs = ContractParser::parse(Rule::function_def, &source).unwrap();

        let pair = pairs.next().unwrap();

        assert_eq!(
            Function::from(pair),
            Function {
                name: String::from("f"),
                recursive: false,
                cases: vec![Case {
                    parameters: vec![],
                    expressions: vec![],
                    return_values: vec![]
                }],
                signature: Signature {
                    inputs: vec![Type::Uint],
                    outputs: vec![Type::Uint, Type::Uint]
                }
            }
        );
    }

    // 	#[test]
    // 	fn simple_function() {
    // 		let source = r#"define g public
    // ({a} b) x :-
    // 	(f (f (and a b)))."#;

    // 		let mut pairs = ContractParser::parse(Rule::function_def, &source).unwrap();

    // 		let pair = pairs.next().unwrap();

    // 		assert_eq!(Function::from(pair),
    // 			Function {
    // 				name: String::from("g"),
    // 				visibility: Visibility::Public,
    // 				cases: vec![
    // 					Case {
    // 						parameters: vec![
    // 							Parameter {
    // 								name: String::from("a"),
    // 								_type: Type::Array,
    // 							},
    // 							Parameter {
    // 								name: String::from("b"),
    // 								_type: Type::Uint,
    // 							}
    // 						],
    // 						return_value: ReturnValue {
    // 							name: String::from("x"),
    // 							_type: Type::Bool
    // 						}
    // 					}
    // 				]
    // 			}
    // 		);
    // 	}
}
