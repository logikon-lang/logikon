extern crate yultsur;

use self::yultsur::*;

use ast;

pub fn logikon_compile(contract: &ast::Contract) -> String {
    let mut statements = vec![];
    yul::Block { statements: statements }.to_string()
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
}
