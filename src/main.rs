mod parsing;


use parsing::preprocessor::Preprocessor;
use parsing::scanner::Scanner;
use parsing::ye;

use crate::parsing::postprocessor::PostProcessor;


#[macro_use] extern crate lalrpop_util;


pub fn main() {
    // let s = String::from("\\mut a->f ((0⚖1-1))");
    let s = String::from("let b = 5; if a { (b + 1) - 2 } else { c }; b;");

    for i in  Preprocessor::new(Scanner::new(&s)) {
        println!("{:?}", i);
    }
    let mut preprocessor_ = Preprocessor::new(Scanner::new(&s));
    let res = ye::InnerBlockParser::new().parse(&s, &mut preprocessor_);
    println!("{:#?}", res);
    let postprocessor_ = PostProcessor { preprocessor: preprocessor_ };
}
