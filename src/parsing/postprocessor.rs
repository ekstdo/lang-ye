use super::{preprocessor::Preprocessor, ast::StmtAST};


// struct to reparse operator order 
// and remove syntactic sugar
pub struct PostProcessor<'a> {
    pub preprocessor: Preprocessor<'a>,
}

impl <'a> PostProcessor<'a> {
    pub fn process(ast: Vec<StmtAST<'a>>) -> Vec<StmtAST<'a>> {
        unimplemented!()
    }
}
