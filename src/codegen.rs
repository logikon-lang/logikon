// NOTE: this assumes "ordered logikon" as an input

extern crate yultsur;

use self::yultsur::yul::*;

use ast;

// Insanely not idiomatic rust. Hackathon mode.
fn get_expression(stmnt: Statement) -> Expression {
    if let Statement::Expression(exp) = stmnt {
        return exp;
    }
    panic!();
}

// Insanely not idiomatic rust. Hackathon mode.
fn get_identifier(exp: Expression) -> Identifier {
    if let Expression::Identifier(identifier) = exp {
        return identifier;
    }
    panic!();
}

// Insanely not idiomatic rust. Hackathon mode.
fn compile_expression(exp: &ast::BooleanExpression) -> Statement {
    match exp {
        ast::BooleanExpression::Identifier(identifier) => {
            Statement::Expression(Expression::Identifier(Identifier {
                identifier: identifier.to_string(),
                yultype: None,
            }))
        }
        ast::BooleanExpression::EqBool(left, right) => {
            let left = get_expression(compile_expression(left));
            let right = get_expression(compile_expression(right));
            // Statement::Expression(Expression::FunctionCall(Identifier::new("eq"), vec![left, right]))
            Statement::Assignment(Assignment{ identifiers: vec![get_identifier(left)], expression: right })
        }
        c => panic!("Unsupported expression: {:?}", c),
    }
}

// Insanely not idiomatic rust. Hackathon mode.
fn compile_case(name: &str, case: &ast::Case) -> Statement {
    let name: Identifier = Identifier {
        identifier: name.to_string(),
        yultype: None,
    };
    let mut parameters: Vec<Identifier> = vec![];
    let mut returns: Vec<Identifier> = vec![];
    let mut block: Block = Block { statements: vec![] };

    for parameter in &case.parameters {
        parameters.push(Identifier {
            identifier: parameter.name.clone(),
            yultype: None,
        });
    }

    returns.push(Identifier {
        identifier: case.return_value.name.clone(),
        yultype: None,
    });

    for expression in &case.expressions {
        block.statements.push(compile_expression(expression));
    }

    Statement::FunctionDefinition(FunctionDefinition{ name, parameters, returns, block })
}

fn compile_function(function: &ast::Function) -> Statement {
    let mut statements = vec![];

    for (i, case) in function.cases.iter().enumerate() {
        let name = format!("{}_{}", function.name, i);
        statements.push(compile_case(&name, case));
    }

    Statement::Block(Block {
        statements: statements,
    })
}

pub fn logikon_compile(contract: &ast::Contract) -> String {
    let mut statements = vec![];

    // Add built in helpers
    statements.push(Statement::FunctionDefinition(FunctionDefinition {
        name: Identifier {
            identifier: "require".to_string(),
            yultype: None,
        },
        parameters: vec![Identifier {
            identifier: "condition".to_string(),
            yultype: None,
        }],
        returns: vec![],
        block: Block {
            statements: vec![
                Statement::If(If {
                    expression: Expression::FunctionCall(FunctionCall {
                        identifier: Identifier {
                            identifier: "not".to_string(),
                            yultype: None
                        },
                        arguments: vec![Expression::Identifier(Identifier {
                            identifier: "condition".to_string(),
                            yultype: None,
                        })],
                    }),
                    block: Block {
                        statements: vec![Statement::Expression(Expression::FunctionCall(FunctionCall {
                            identifier: Identifier {
                                identifier: "revert".to_string(),
                                yultype: None
                            },
                            arguments: vec![Expression::Literal(Literal {
                                literal: "0".to_string(),
                                yultype: None,
                            }), Expression::Literal(Literal {
                                literal: "0".to_string(),
                                yultype: None,
                            })],
                        }))]
                    }
                })
            ]
        }
    }));

    for function in &contract.functions {
        statements.push(compile_function(&function))
    }

    Block {
        statements: statements,
    }.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn smoke() {
        let source = "";

        assert_eq!(logikon_compile(&ast::logikon_parse(&source)), "{ function require(condition) { if not(condition) { revert(0, 0) } } }");
    }

    #[test]
    fn identity_fn() {
        let source = r#"define f (Bool) -> Bool
        case (a) x :-
            (= x a)."#;

        assert_eq!(
            logikon_compile(&ast::logikon_parse(&source)),
            "{ function require(condition) { if not(condition) { revert(0, 0) } } { function f_0(a) -> x { x := a } } }"
        );
    }
}
