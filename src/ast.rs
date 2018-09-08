use std::collections::HashMap;

#[derive(Hash, PartialEq, Debug)]
pub struct Contract {
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

#[derive(Hash, PartialEq, Debug, Clone)]
struct Case {
    parameters: Vec<Variable>, // TODO implement patterns
    expressions: Vec<BooleanExpression>,
    return_value: Variable,
}

#[derive(Hash, PartialEq, Debug, Clone)]
enum BooleanExpression {
    Identifier(String),

    EqBool(Box<BooleanExpression>, Box<BooleanExpression>),
    NeBool(Box<BooleanExpression>, Box<BooleanExpression>),
    EqUint(Box<UintExpression>, Box<UintExpression>),
    NeUint(Box<UintExpression>, Box<UintExpression>),
    Lt(Box<UintExpression>, Box<UintExpression>),
    Gt(Box<UintExpression>, Box<UintExpression>),
    Le(Box<UintExpression>, Box<UintExpression>),
    Ge(Box<UintExpression>, Box<UintExpression>),

    And(Box<BooleanExpression>, Box<BooleanExpression>),
    Or(Box<BooleanExpression>, Box<BooleanExpression>),
    Not(Box<BooleanExpression>),
    Ite(
        Box<BooleanExpression>,
        Box<BooleanExpression>,
        Box<BooleanExpression>,
    ),

    FunctionCall(String, Vec<Expression>),
}

#[derive(Hash, PartialEq, Debug, Clone)]
enum Expression {
    Boolean(BooleanExpression),
    Uint(UintExpression),
}

impl From<BooleanExpression> for Expression {
    fn from(e: BooleanExpression) -> Expression {
        Expression::Boolean(e)
    }
}

impl From<UintExpression> for Expression {
    fn from(e: UintExpression) -> Expression {
        Expression::Uint(e)
    }
}

#[derive(Hash, PartialEq, Debug, Clone)]
enum UintExpression {
    Identifier(String),

    Plus(Box<UintExpression>, Box<UintExpression>),
    Minus(Box<UintExpression>, Box<UintExpression>),
    Times(Box<UintExpression>, Box<UintExpression>),
    Div(Box<UintExpression>, Box<UintExpression>),

    Ite(
        Box<BooleanExpression>,
        Box<UintExpression>,
        Box<UintExpression>,
    ),

    FunctionCall(String, Vec<Expression>),

    Select(Box<ArrayExpression>, Box<UintExpression>),
}

#[derive(Hash, PartialEq, Debug, Clone)]
enum ArrayExpression {
    Identifier(String),
    Store(
        Box<ArrayExpression>,
        Box<UintExpression>,
        Box<UintExpression>,
    ),
}

#[derive(Hash, PartialEq, Debug, Clone)]
struct Variable {
    name: String,
    _type: Type,
}

#[derive(Hash, PartialEq, Debug, Clone)]
enum Type {
    Unknown,
    Uint,
    Array,
    Bool,
    List,
}

#[derive(Hash, PartialEq, Debug)]
struct Signature {
    inputs: Vec<Type>,
    output: Type,
}

impl<'a> Type {
    fn from(pair: Pair<Rule>) -> Type {
        match pair.as_rule() {
            Rule::logikon_type => match pair.as_str() {
                "Uint" => Type::Uint,
                "Bool" => Type::Bool,
                "List" => Type::List,
                "Array" => Type::Array,
                _ => panic!("die"),
            },
            _ => panic!("not a type"),
        }
    }
}

impl<'a> Contract {
    fn from(pair: Pair<Rule>) -> Contract {
        let mut state: Vec<StateVariable> = vec![];
        let mut functions: Vec<Function> = vec![];

        let mut symbols = HashMap::new();

        for p in pair.clone().into_inner() {
            match p.as_rule() {
                Rule::function_def => {
                    let name_pair = p.clone().into_inner().find(|t| match t.as_rule() {
                        Rule::function_identifier => true,
                        _ => false
                    }).unwrap();


                    let type_pair = match p.clone().into_inner().find(|t| match t.as_rule() {
                        Rule::logikon_type => true,
                        _ => false
                    }).unwrap().as_str() {
                        "Uint" => Type::Uint,
                        "Bool" => Type::Bool,
                        _ => panic!("Unknown type")
                    };

                    let input_types = p.into_inner().find(|t| match t.as_rule() {
                        Rule::type_list => true,
                        _ => false
                    }).unwrap().into_inner().map(|t| match t.as_rule() {
                        Rule::logikon_type => t.as_str(),
                        _ => panic!("")
                    }).fold(vec![], |mut acc, e| {
                        acc.extend(vec![match e {
                            "Uint" => Type::Uint,
                            "Bool" => Type::Bool,
                            _ => panic!("Unknown type")
                        }]);
                        acc
                    });

                    symbols.insert(String::from(name_pair.as_str()), Signature { output: type_pair, inputs: input_types });
                },
                _ => panic!("")
            }
        }

        for p in pair.into_inner() {
            match p.as_rule() {
                Rule::state_var_decl => {
                    state.push(StateVariable::from(p));
                }
                Rule::function_def => {
                    functions.push(Function::from(p, &symbols));
                }
                c => panic!("{:?}", c),
            }
        }

        Contract {
            state,
            functions,
        }
    }
}

impl<'a> StateVariable {
    fn from(pair: Pair<Rule>) -> StateVariable {
        let mut name = String::new();
        let mut _type = Type::Unknown;

        for p in pair.into_inner() {
            match p.as_rule() {
                Rule::identifier => {
                    name = p.as_str().to_string();
                }
                Rule::logikon_type => {
                    _type = Type::from(p);
                }
                c => panic!("{:?}", c),
            }
        }

        StateVariable {
            name,
            _type
        }
    }
}

impl<'a> Function {
    fn from(pair: Pair<Rule>, symbols: &HashMap<String, Signature>) -> Function {
        let mut name = String::new();
        let mut cases: Vec<Case> = vec![];
        let mut recursive = false;
        let mut inputs = vec![];
        let mut output = Type::Unknown;

        for p in pair.into_inner() {
            match p.as_rule() {
                Rule::identifier => {
                    name = p.as_str().to_string();
                }
                Rule::case => {
                    cases.push(Case::from(p, HashMap::new()));
                }
                Rule::recursive => {
                    recursive = true;
                }
                Rule::type_list => {
                    for t in p.into_inner() {
                        inputs.push(Type::from(t))
                    }
                }
                Rule::logikon_type => {
                    output = Type::from(p);
                }
                c => panic!("{:?}", c),
            }
        }

        let cases = cases.iter().map(|c| Case {
            parameters: c.parameters.iter().enumerate().map(|(index, v)| Variable {
                _type: inputs[index].clone(),
                name: v.name.clone(),
            }).collect(),
            return_value: Variable {
                _type: output.clone(),
                name: c.return_value.name.clone()
            },
            expressions: c.expressions.clone()
        }).collect();

        Function {
            name,
            recursive,
            cases,
            signature: Signature { inputs, output },
        }
    }
}

impl<'a> Variable {
    fn from(pair: Pair<Rule>) -> Variable {
        Variable {
            name: String::from(pair.as_str()),
            _type: Type::Unknown,
        }
    }
}

impl<'a> UintExpression {
    fn from(pair: Pair<Rule>, symbols: &HashMap<String, Signature>) -> UintExpression {
        let mut arg_count = 0;

        let mut token_iter = pair.into_inner();

        let op = token_iter.next().unwrap();

        match op.as_rule() {
            Rule::identifier => UintExpression::Identifier(String::from(op.as_str())),
            Rule::statement => UintExpression::from(op, &symbols),
            Rule::function_identifier => match symbols.get(op.as_str()).unwrap().output {
                Type::Uint => UintExpression::FunctionCall(String::from(op.as_str()), vec![]),
                _ => panic!("")
            }
            Rule::binary_op => {
                let argument1 = token_iter.next().unwrap();
                let argument2 = token_iter.next().unwrap();

                match op.as_str() {
                    "+" => UintExpression::Plus(
                        Box::new(UintExpression::from(argument1, &symbols)),
                        Box::new(UintExpression::from(argument2, &symbols)),
                    ),
                    "-" => UintExpression::Minus(
                        Box::new(UintExpression::from(argument1, &symbols)),
                        Box::new(UintExpression::from(argument2, &symbols)),
                    ),
                    "*" => UintExpression::Times(
                        Box::new(UintExpression::from(argument1, &symbols)),
                        Box::new(UintExpression::from(argument2, &symbols)),
                    ),
                    "/" => UintExpression::Div(
                        Box::new(UintExpression::from(argument1, &symbols)),
                        Box::new(UintExpression::from(argument2, &symbols)),
                    ),
                    "select" => UintExpression::Select(
                        Box::new(ArrayExpression::from(argument1, &symbols)),
                        Box::new(UintExpression::from(argument2, &symbols)),
                    ),
                    _ => panic!(""),
                }
            }
            Rule::ternary_op => {
                let argument1 = token_iter.next().unwrap();
                let argument2 = token_iter.next().unwrap();
                let argument3 = token_iter.next().unwrap();

                match op.as_str() {
                    "ite" => UintExpression::Ite(
                        Box::new(BooleanExpression::from(argument1, &symbols)),
                        Box::new(UintExpression::from(argument2, &symbols)),
                        Box::new(UintExpression::from(argument3, &symbols)),
                    ),
                    _ => panic!(""),
                }
            }
            _ => panic!(""),
        }
    }
}

impl<'a> ArrayExpression {
    fn from(pair: Pair<Rule>, symbols: &HashMap<String, Signature>) -> ArrayExpression {
        let mut token_iter = pair.into_inner();

        let op = token_iter.next().unwrap();

        match op.as_rule() {
            Rule::function_identifier => panic!(""),
            Rule::ternary_op => {
                let argument1 = token_iter.next().unwrap();
                let argument2 = token_iter.next().unwrap();
                let argument3 = token_iter.next().unwrap();

                match op.as_str() {
                    "store" => ArrayExpression::Store(
                        Box::new(ArrayExpression::from(argument1, &symbols)),
                        Box::new(UintExpression::from(argument2, &symbols)),
                        Box::new(UintExpression::from(argument3, &symbols)),
                    ),
                    _ => panic!(""),
                }
            }
            _ => panic!(""),
        }
    }
}

impl<'a> BooleanExpression {
    fn from(pair: Pair<Rule>, symbols: &HashMap<String, Signature>) -> BooleanExpression {
        let mut token_iter = pair.into_inner();

        let op = token_iter.next().unwrap();

        match op.as_rule() {
            Rule::statement => BooleanExpression::from(op, &symbols),
            Rule::identifier => BooleanExpression::Identifier(String::from(op.as_str())),
            Rule::function_identifier => {

                let input_types = &symbols.get(op.as_str()).unwrap().inputs;

                for (index, t) in input_types.iter().enumerate() {
                    let argument = token_iter.next().unwrap();

                }

                match symbols.get(op.as_str()).unwrap().output {
                    Type::Bool => BooleanExpression::FunctionCall(String::from(op.as_str()), vec![]),
                    _ => panic!("")
                }
            }            
            Rule::unary_op => {
                let argument = token_iter.next().unwrap();
                match op.as_str() {
                    "prove" => panic!("NO PROVE"),
                    "not" => BooleanExpression::Not(Box::new(BooleanExpression::from(argument, &symbols))),
                    _ => panic!(""),
                }
            }
            Rule::binary_op => {
                let argument1 = token_iter.next().unwrap();
                let argument2 = token_iter.next().unwrap();

                match op.as_str() {
                    "<=" => BooleanExpression::Le(
                        Box::new(UintExpression::from(argument1, &symbols)),
                        Box::new(UintExpression::from(argument2, &symbols)),
                    ),
                    ">=" => BooleanExpression::Ge(
                        Box::new(UintExpression::from(argument1, &symbols)),
                        Box::new(UintExpression::from(argument2, &symbols)),
                    ),
                    "=" => BooleanExpression::EqBool(
                        Box::new(BooleanExpression::from(argument1, &symbols)),
                        Box::new(BooleanExpression::from(argument2, &symbols)),
                    ),
                    "!=" => BooleanExpression::NeBool(
                        Box::new(BooleanExpression::from(argument1, &symbols)),
                        Box::new(BooleanExpression::from(argument2, &symbols)),
                    ),
                    "==" => BooleanExpression::EqUint(
                        Box::new(UintExpression::from(argument1, &symbols)),
                        Box::new(UintExpression::from(argument2, &symbols)),
                    ),
                    "!==" => BooleanExpression::NeUint(
                        Box::new(UintExpression::from(argument1, &symbols)),
                        Box::new(UintExpression::from(argument2, &symbols)),
                    ),
                    ">" => BooleanExpression::Gt(
                        Box::new(UintExpression::from(argument1, &symbols)),
                        Box::new(UintExpression::from(argument2, &symbols)),
                    ),
                    "<" => BooleanExpression::Lt(
                        Box::new(UintExpression::from(argument1, &symbols)),
                        Box::new(UintExpression::from(argument2, &symbols)),
                    ),
                    _ => panic!(""),
                }
            }
            Rule::ternary_op => {
                let argument1 = token_iter.next().unwrap();
                let argument2 = token_iter.next().unwrap();
                let argument3 = token_iter.next().unwrap();

                match op.as_str() {
                    "ite" => BooleanExpression::Ite(
                        Box::new(BooleanExpression::from(argument1, &symbols)),
                        Box::new(BooleanExpression::from(argument2, &symbols)),
                        Box::new(BooleanExpression::from(argument3, &symbols)),
                    ),
                    _ => panic!(""),
                }
            }
            e => panic!("{:?}", e),
        }
    }
}

impl<'a> Case {
    fn from(pair: Pair<Rule>, symbols: HashMap<String, Signature>) -> Case {
        let mut parameters = vec![];
        let mut return_value = Variable { name: String::new(), _type: Type::Unknown };
        let mut expressions = vec![];

        for p in pair.into_inner() {
            match p.as_rule() {
                Rule::return_value => {
                    return_value = Variable::from(p);
                }
                Rule::parameter_list => {
                    for t in p.into_inner() {
                        parameters.push(Variable::from(t))
                    }
                }
                Rule::case_body => {
                    for t in p.into_inner() {
                        expressions.push(BooleanExpression::from(t, &symbols));
                    }
                }
                c => panic!("{:?}", c),
            }
        }

        Case {
            parameters,
            expressions,
            return_value,
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

pub fn logikon_parse(source: &str) -> Contract {
    let mut pairs = ContractParser::parse(Rule::contract, &source).unwrap();
    Contract::from(pairs.next().unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn statevar() {
        let source = r#"declare Balance Array."#;

        let mut pairs = ContractParser::parse(Rule::state_var_decl, &source).unwrap();

        let pair = pairs.next().unwrap();

        assert_eq!(
            StateVariable::from(pair),
            StateVariable {
                name: String::from("Balance"),
                _type: Type::Array,
            }
        );
    }

    #[test]
    fn empty_function() {
        let source = r#"define f (Uint) -> Uint
		case () _.
	"#;

        let mut pairs = ContractParser::parse(Rule::function_def, &source).unwrap();

        let pair = pairs.next().unwrap();

        assert_eq!(
            Function::from(pair, &HashMap::new()),
            Function {
                name: String::from("f"),
                recursive: false,
                cases: vec![Case {
                    parameters: vec![],
                    expressions: vec![],
                    return_value: Variable { name: String::from("_"), _type: Type::Uint }
                }],
                signature: Signature {
                    inputs: vec![Type::Uint],
                    output: Type::Uint
                }
            }
        );
    }

    #[test]
    fn identity_function() {
        let source = r#"define f (Bool) -> Bool 
        case (a) x :-
            (= x y).
    "#;

        let mut pairs = ContractParser::parse(Rule::function_def, &source).unwrap();

        let pair = pairs.next().unwrap();

        assert_eq!(
            Function::from(pair, &HashMap::new()),
            Function {
                name: String::from("f"),
                recursive: false,
                cases: vec![Case {
                    parameters: vec![Variable {
                        name: String::from("a"),
                        _type: Type::Bool
                    }],
                    expressions: vec![BooleanExpression::EqBool(
                        Box::new(BooleanExpression::Identifier(String::from("x"))),
                        Box::new(BooleanExpression::Identifier(String::from("y")))
                    )],
                    return_value: Variable {
                        name: String::from("x"),
                        _type: Type::Bool
                    }
                }],
                signature: Signature {
                    inputs: vec![Type::Bool],
                    output: Type::Bool
                }
            }
        );
    }

    #[test]
    fn ite_function() {
        let source = r#"define f (Bool) -> Bool 
        case (a) x :-
            (= x (ite a a a)).
    "#;

        let mut pairs = ContractParser::parse(Rule::function_def, &source).unwrap();

        let pair = pairs.next().unwrap();

        assert_eq!(
            Function::from(pair, &HashMap::new()),
            Function {
                name: String::from("f"),
                recursive: false,
                cases: vec![Case {
                    parameters: vec![Variable {
                        name: String::from("a"),
                        _type: Type::Bool
                    }],
                    expressions: vec![BooleanExpression::EqBool(
                        Box::new(BooleanExpression::Identifier(String::from("x"))),
                        Box::new(BooleanExpression::Ite(
                            Box::new(BooleanExpression::Identifier(String::from("a"))),
                            Box::new(BooleanExpression::Identifier(String::from("a"))),
                            Box::new(BooleanExpression::Identifier(String::from("a"))),
                        ))
                    )],
                    return_value: Variable {
                        name: String::from("x"),
                        _type: Type::Bool
                    }
                }],
                signature: Signature {
                    inputs: vec![Type::Bool],
                    output: Type::Bool
                }
            }
        );
    }

    #[test]
    fn ite_uint_function() {
        let source = r#"define f (Uint Bool) -> Uint
        case (a b) x :-
            (== x (ite b a a)).
    "#;

        let mut pairs = ContractParser::parse(Rule::function_def, &source).unwrap();

        let pair = pairs.next().unwrap();

        assert_eq!(
            Function::from(pair, &HashMap::new()),
            Function {
                name: String::from("f"),
                recursive: false,
                cases: vec![Case {
                    parameters: vec![
                        Variable {
                            name: String::from("a"),
                            _type: Type::Uint
                        },
                        Variable {
                            name: String::from("b"),
                            _type: Type::Bool
                        }
                    ],
                    expressions: vec![BooleanExpression::EqUint(
                        Box::new(UintExpression::Identifier(String::from("x"))),
                        Box::new(UintExpression::Ite(
                            Box::new(BooleanExpression::Identifier(String::from("b"))),
                            Box::new(UintExpression::Identifier(String::from("a"))),
                            Box::new(UintExpression::Identifier(String::from("a"))),
                        ))
                    )],
                    return_value: Variable {
                        name: String::from("x"),
                        _type: Type::Uint
                    }
                }],
                signature: Signature {
                    inputs: vec![Type::Uint, Type::Bool],
                    output: Type::Uint
                }
            }
        );
    }

    #[test]
    fn function_call() {
        let source = r#"define min (Uint Uint) -> Uint
                        case (a b) x :-
                            (== x (ite (< a b) a b)).

                        define forward (Uint Uint) -> Uint
                        case (a b) x :-
                            (== x (min a b)).
        "#;

        let mut pairs = ContractParser::parse(Rule::contract, &source).unwrap();

        let pair = pairs.next().unwrap();

        assert_eq!(
            Contract::from(pair),
            Contract {
                state: vec![], 
                functions : vec![Function {
                    name: String::from("min"),
                    recursive: false,
                    cases: vec![Case {
                        parameters: vec![
                            Variable {
                                name: String::from("a"),
                                _type: Type::Uint
                            },
                            Variable {
                                name: String::from("b"),
                                _type: Type::Uint
                            }
                        ],
                        expressions: vec![BooleanExpression::EqUint(
                            Box::new(UintExpression::Identifier(String::from("x"))),
                            Box::new(UintExpression::Ite(
                                Box::new(BooleanExpression::Lt(
                                    Box::new(UintExpression::Identifier(String::from("a"))),
                                    Box::new(UintExpression::Identifier(String::from("b")))
                                )),
                                Box::new(UintExpression::Identifier(String::from("a"))),
                                Box::new(UintExpression::Identifier(String::from("b"))),
                            ))
                        )],
                        return_value: Variable {
                            name: String::from("x"),
                            _type: Type::Uint
                        }
                    }],
                    signature: Signature {
                        inputs: vec![Type::Uint, Type::Uint],
                        output: Type::Uint
                    }
                }, Function {
                    name: String::from("forward"),
                    recursive: false,
                    cases: vec![Case {
                        parameters: vec![
                            Variable {
                                name: String::from("a"),
                                _type: Type::Uint
                            },
                            Variable {
                                name: String::from("b"),
                                _type: Type::Uint
                            }
                        ],
                        expressions: vec![BooleanExpression::EqUint(
                            Box::new(UintExpression::Identifier(String::from("x"))),
                            Box::new(UintExpression::FunctionCall(
                                String::from("min"), vec![
                                    UintExpression::Identifier(String::from("a")).into(),
                                    UintExpression::Identifier(String::from("b")).into(),
                                ]
                            ))
                        )],
                        return_value: Variable {
                            name: String::from("x"),
                            _type: Type::Uint
                        }
                    }],
                    signature: Signature {
                        inputs: vec![Type::Uint, Type::Uint],
                        output: Type::Uint
                    }
                }
            ]}
        );
    }

    #[test]
    fn contract() {
        let source = r#"declare Balance Array.

        define f (Uint) -> Uint
            case () _."#;

        let mut pairs = ContractParser::parse(Rule::contract, &source).unwrap();

        let pair = pairs.next().unwrap();

        assert_eq!(
            Contract::from(pair),
            Contract {
                state: vec![StateVariable {
                    name: String::from("Balance"),
                    _type: Type::Array,
                }],
                functions: vec![Function {
                    name: String::from("f"),
                    recursive: false,
                    cases: vec![Case {
                        parameters: vec![],
                        expressions: vec![],
                        return_value: Variable { name: String::from("_"), _type: Type::Uint }
                    }],
                    signature: Signature {
                        inputs: vec![Type::Uint],
                        output: Type::Uint
                    }
                }],
            }
        );
    }

    #[test]
    fn public_api() {
        let source = r#"define f (Bool) -> Bool 
        case (a) x :-
            (= x y).
    "#;

        let contract = logikon_parse(&String::from(source));

        assert_eq!(
            contract,
            Contract {
                state: vec![],
                functions: vec![Function {
                    name: String::from("f"),
                    recursive: false,
                    cases: vec![Case {
                        parameters: vec![Variable {
                            name: String::from("a"),
                            _type: Type::Bool
                        }],
                        expressions: vec![BooleanExpression::EqBool(
                            Box::new(BooleanExpression::Identifier(String::from("x"))),
                            Box::new(BooleanExpression::Identifier(String::from("y")))
                        )],
                        return_value: Variable {
                            name: String::from("x"),
                            _type: Type::Bool
                        }
                    }],
                    signature: Signature {
                        inputs: vec![Type::Bool],
                        output: Type::Bool
                    }
                }],
            }
        );
    }
}
