use std::collections::HashMap;

use super::{token::{Spanned, Token}, scanner::LexErr};

use super::scanner::{Scanner, LexResult};

pub struct Preprocessor<'a> {
    pub scanner: Scanner<'a>,
    pub infix_op: HashMap<String, (usize, usize)>,
    pub prefix_op: HashMap<String, usize>,
    pub postfix_op: HashMap<String, usize>
}

#[derive(Clone, Debug)]
pub enum PreprocessorError {
    Lexer(LexErr),
    Expected(Token<'static>)
}

impl <'a> Preprocessor<'a> {
    pub fn new(scanner: Scanner<'a>) -> Self {
        let infix_op = HashMap::from([
            // (String::from(","), (5, 6)), // gone    
            // (String::from("=>"), (7, 8)), // gone 
            // (String::from("="), (8, 7)),
            // (String::from("|"), (10, 9)),
            (String::from("<-"), (11, 12)),   // backpassing

            // (String::from("in"), (15, 9)),

            (String::from("<|"), (10, 9)),   // low prec operator
            (String::from("<||"), (10, 9)),  // uncurry
            (String::from("<|||"), (10, 9)), // uncurry2
            (String::from(">>="), (11, 12)),  // monad chain
            (String::from("|>"), (13, 14)),  // pipe
            (String::from("||>"), (13, 14)), // uncurry pipe
            (String::from("|||>"), (13, 14)),// uncurry2 pipe
            (String::from(":"), (15, 16)),  // type 
            (String::from(":>"), (15, 16)),  // into 
            // (String::from("->"), (16, 15)), // function type operator
            (String::from(".."), (17, 18)), // from to
            (String::from("..="), (17, 18)),// from to including right end
            (String::from("||"), (19, 20)), // or
            (String::from("^^"), (19, 20)),
            (String::from("^^"), (19, 20)),
            (String::from("&&"), (21, 22)),
            (String::from("~|"), (23, 24)),
            (String::from("~^"), (23, 24)),
            (String::from("~&"), (25, 26)),
            (String::from("=="), (27, 28)),
            (String::from("<="), (27, 28)),
            (String::from(">="), (27, 28)),
            (String::from("!="), (27, 28)),
            (String::from("==="), (27, 28)),
            (String::from("<"), (27, 28)),
            (String::from(">"), (27, 28)),
            (String::from("<$>"), (29, 30)),// functor map
            (String::from("<*>"), (29, 30)),// applicative liftA6
            (String::from("++"), (31, 32)), // list concat
            (String::from("<>"), (31, 32)), // monoid operation
            (String::from("::"), (32, 31)), // list prepend
            (String::from("~>"), (33, 34)),
            (String::from("<~"), (33, 34)), // bitwise shifts
            (String::from("+"), (35, 36)),  // addition 
            (String::from("-"), (35, 36)),  // subtraction
            (String::from("*"), (37, 38)),  // multiplication
            (String::from("/"), (37, 38)),  // division
            (String::from("%"), (37, 38)),  // modulo
            (String::from("%%"), (37, 38)), // ratio
            (String::from("^"), (40, 39)),  // exponentiation
            (String::from("."), (45, 46)),  // object getter 
            (String::from("!!"), (47, 48)), // array indexing
        ]);
        let prefix_op = HashMap::from([
            (String::from("+"), (39)),
            (String::from("-"), (39)),
            (String::from("!"), (39)),
            (String::from("~!"), (39)),
        ]);
        let postfix_op = HashMap::from([
            (String::from("?"), (39)),
        ]);

        Self { scanner, infix_op, prefix_op, postfix_op }
    }

    fn expect(&mut self, tok: Token<'static>) -> Result<bool, PreprocessorError> {
        let next_tok = self.scanner.next().ok_or(PreprocessorError::Expected(tok))?.map_err(PreprocessorError::Lexer)?;
        if next_tok.1 == tok {
            Ok(true)
        } else {
            Err(PreprocessorError::Expected(tok))
        }

    }

    fn expect_fun<F>(&mut self, fun: F, err: PreprocessorError) -> Result<Token<'a>, PreprocessorError>
    where F: Fn(&Token<'a>) -> bool {
        let next_tok = self.scanner.next().ok_or(err.clone())?.map_err(PreprocessorError::Lexer)?;
        if fun(&next_tok.1) {
            Ok(next_tok.1)
        } else {
            Err(err)
        }

    }
}

impl<'a> Iterator for Preprocessor<'a> {
    type Item = Spanned<Token<'a>, usize, PreprocessorError>;

    fn next(&mut self) -> Option<Self::Item> {
        macro_rules! expect {
            ($e: expr) => {
                if let Err(e) = self.expect($e) {
                    return Some(Err(e));
                }
            };

            ($e: ident, $p: pat) => {
                let $e = match self.expect_fun(|t: &Token<'a>| {
                    match t {
                        $p => true,
                        _ => false
                    }
                }, PreprocessorError::Expected(Token::Operator("_"))) {
                    Ok(o) => o,
                    Err(e) => { return Some(Err(e)); }
                };

            }
        }
        match self.scanner.next()? {
            Err(e) => Some(Err(PreprocessorError::Lexer(e))),
            Ok(tok) => {
                match tok.1 {
                    Token::Tag("infix") => {
                        expect!(Token::ParenLeft);
                        expect!(operator, Token::Operator(_)); 
                        expect!(Token::Comma);
                        expect!(lprec, Token::Integer(_));
                        expect!(Token::Comma);
                        expect!(rprec, Token::Integer(_));
                        expect!(Token::ParenRight);

                        match (operator, lprec, rprec) {
                            (Token::Operator(o), Token::Integer(lstr), Token::Integer(rstr)) => {
                                let l = str::parse::<usize>(lstr).unwrap();
                                let r = str::parse::<usize>(rstr).unwrap();
                                self.infix_op.insert(o.to_owned(), (l, r));
                            }
                            _ => {}
                        }
                        self.next()
                    }
                    Token::Tag(s) => {
                        todo!()
                    }
                    _ => Some(Ok(tok))
                }
            }
        }
    }
}
