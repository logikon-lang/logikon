extern crate yultsur;

use self::yultsur::yul::*;

use ast;

fn compile_case(name: &str, case: &ast::Case) -> Statement {
    let name:Identifier = Identifier { identifier: name.to_string() };
    let mut parameters:Vec<Identifier> = vec![];
    let mut returns:Vec<Identifier> = vec![];
    let mut block:Block = Block { statements: vec![] };

    for parameter in &case.parameters {
        parameters.push(Identifier { identifier: parameter.name.clone() });
    }

    returns.push(Identifier { identifier: case.return_value.name.clone() });

    // FIXME: translate case.expressions -> block.statements

    Statement::FunctionDefinition(
        name,
        parameters,
        returns,
        block
    )
}

fn compile_function(function: &ast::Function) -> Statement {
    let mut statements = vec![];

    for (i, case) in function.cases.iter().enumerate() {
        let name = format!("{}_{}", function.name, i);
        statements.push(compile_case(&name, case));
    }

    Statement::Block(Block { statements: statements })
}

pub fn logikon_compile(contract: &ast::Contract) -> String {
    let mut statements = vec![];

    for function in &contract.functions {
        statements.push(compile_function(&function))
    }

    Block { statements: statements }.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn smoke() {
        let source = "";

        assert_eq!(
            logikon_compile(&ast::logikon_parse(&source)),
            "{ }"
        );
    }

    #[test]
    fn identity_fn() {
        let source = r#"define f (Bool) -> Bool
        case (a) x :-
            (= x a)."#;

        assert_eq!(
            logikon_compile(&ast::logikon_parse(&source)),
            "{ { function f_0(a) -> (x) { } } }"
        );
    }
}
