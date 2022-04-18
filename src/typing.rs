use crate::parser;

use parser::ASTType;

pub struct Trait {
    name: String
}

pub enum Type {
    Single(String),
    Application(String, Vec<Type>),
    Var(String),
    Conditioned(Box<Type>, Trait)
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedAST<'a> {
    pub pos_marker: parser::Token<'a>,
    pub ttype: Box<ASTType<'a, TypedAST<'a>>>
}
