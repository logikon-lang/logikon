extern crate yultsur;

use self::yultsur::yul::*;

use ast;

fn compile_function(function: &ast::Function) -> Statement {
    let name:Identifier = Identifier { identifier: function.name.clone() };
    let block:Block = Block { statements: vec![] };

    Statement::FunctionDefinition(
        name.clone(),
        vec![],
        vec![],
        block
    )
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
            "{ }"
        );
    }
}
