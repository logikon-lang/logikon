use ast;

pub fn logikon_compile(contract: &ast::Contract) -> String {
    String::from("{}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn smoke() {
        let source = "";

        assert_eq!(
            logikon_compile(&ast::logikon_parse(&source)),
            "{}"
        );
    }
}
