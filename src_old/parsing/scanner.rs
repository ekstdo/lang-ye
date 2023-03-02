use std::{str::CharIndices, iter::Peekable};
use super::token::Token;

pub type Spanned<Tok, Loc, Error> = Result<(Loc, Tok, Loc), Error>;

pub enum LexErr {
    EOF
}

pub type LexResult<'a> = Result<Token<'a>, LexErr>;


fn escapeable(c: char) -> bool {
    c == 'n' || c == 't' || c == 'w' || c == 'b' || c == 'f' || c == 'v' || c == '0' || c == 'r'
}


pub struct Scanner<'a> {
    current_line: usize,
    current_line_pos: usize,
    pub iterator: Peekable<CharIndices<'a>>,
    string: &'a String,
    current_char_pos: usize,
    current_char_size: usize,
    pub cache: Vec<Token<'a>>
}



impl<'a> Scanner<'a> {
    pub fn new(text: &'a String) -> Scanner<'a> {
        Scanner { 
            current_line_pos: 0, 
            current_line: 0, 
            current_char_pos: 0, 
            iterator: text.char_indices().peekable(), 
            string: text,
            current_char_size: 1,
            cache: Vec::new() }
    }

    fn var_match(s: &'a str) -> Token {
        if s.starts_with('#') {
            return Token::Tag;
        }
        match s {
            "let" => Token::Let,
            "if" => Token::If,
            "else" => Token::Else,
            "while" => Token::While,
            "for" => Token::For,
            "raw" => Token::Raw,
            "mut" => Token::Mut,
            "return" => Token::Return,
            "continue" => Token::Continue,
            "break" => Token::Break,
            "ref" => Token::Ref,
            "is" => Token::Is,
            "in" => Token::In,
            "static" => Token::Static,
            "export" => Token::Export,
            "import" => Token::Import,
            "lazy" => Token::Lazy,
            "async" => Token::Async,
            "goto" => Token::Goto,
            "here" => Token::Here,
            "await" => Token::Await,
            _ => Token::Variable(s)
        }
    }

    fn next_char(&mut self) -> Option<char> {
        self.current_line_pos += 1;
        let result = self.iterator.next();
        match result {
            Some((u, v)) => {self.current_char_pos = u; self.current_char_size = v.len_utf8(); Some(v)},
            _ => None
        }
    }

    fn expect_char(&mut self) -> Result<char, LexErr> {
        self.next_char().ok_or(LexErr::EOF)
    }

    fn peek_char(&mut self) -> Option<char> {
        self.iterator.peek().map(|x| x.1)
    }

    fn new_line(&mut self) {
        self.current_line_pos = 0;
        self.current_line += 1;
    }

    pub fn make_token<F>(&mut self, tokenFn: F, offset: usize) -> (usize, Token<'a>, usize)
    where F: Fn(&'a str) -> Token<'a> {
        let end = self.current_char_pos + self.current_char_size - 1;
        let res = (offset, tokenFn(&self.string[offset..=end]), end);

        self.current_char_pos += 1;
        res
    }

    pub fn get_pos(&self) -> (usize, usize) {
        (self.current_line_pos, self.current_char_pos)
    }

    fn get_char(&mut self, offset: usize) -> LexResult<'a> {
        let c = self.expect_char()?;
        let e = (String::from("invalid character"), self.get_pos());
        if c == '\\' {
            let c = self.expect_char()?;
            if escapeable(c) || c == '\'' {
            } else if c == 'x' || c == 'o' || c == 'b' || c.is_digit(10) {
                let radix = if c == 'x' {16} else if c == 'o' {8} else if c == 'b' {2} else {10};
                while self.expect_char()?.is_digit(radix) {
                }

            } else { return Err(e); }

            if self.expect_char()? == '\'' {
                if c == '\n' { self.new_line(); }
                Ok(self.make_token(|s| TokenType::Char(c), offset))
            } else {
                Err(e)
            }

        } else if self.expect_char()? == '\'' {
            Ok(self.make_token(|s| TokenType::Char(c), offset))
        } else {
            Err(e)
        }
    }

    fn get_string(&mut self, offset: usize) -> LexResult<'a> {
        let mut cur_char = self.expect_char()?;
        while cur_char != '"' {
            if cur_char == '\n' {
                self.new_line();
            } else if cur_char == '\\' {
                let next_char = self.expect_char()?;
                if escapeable(next_char) || next_char == '"' {
                } else if next_char == 'x' || next_char == 'o' || next_char.is_digit(10) {
                    let radix = if next_char == 'x' {16} else if next_char == 'o' {8} else {10};
                    while self.expect_char()?.is_digit(radix) {
                    }
                } else {
                    return Err((String::from("invalid String, sth is not escaped!"), self.get_pos()));
                }
            }

            if cur_char == '"' {
                break;
            }

            cur_char = self.expect_char()?;
        }
        Ok(self.make_token(|s| TokenType::Str(s), offset))
    }

    fn get_var(&mut self, offset: usize) -> LexResult<'a> {
        let mut c = self.peek_char();
        loop {
            match c {
                Some(d) if d.is_alphanumeric() => {
                    self.next_char();
                    c = self.peek_char();
                    continue;
                },
                _ => {
                    return Ok(self.make_token(Scanner::var_match, offset))
                }
            }
        }
    }

    fn get_op(&mut self, offset: usize) -> LexResult<'a> {
        let mut c = self.peek_char();
        loop {
            match c {
                Some(d) if !d.is_alphanumeric() && !d.is_whitespace() && d != '(' && d != '#' && d != '' && d != ')' => {
                    self.next_char();
                    c = self.peek_char();
                    continue;
                },
                _ => {
                    let slice = &self.string[offset..=self.current_char_pos+self.current_char_size - 1];
                    return Ok(self.make_token(if slice == "=" || slice == "≔" { |_| TokenType::Assign} else if slice.ends_with('=') {TokenType::Reassign} else {|_| TokenType::Operator}, offset))
                }
            }
        }
    }

    fn get_number(&mut self, offset: usize) -> LexResult<'a> {
        let mut float = false;
        let mut exp = false;
        let mut exp_float = false;
        let mut just_exp = 0;
        let mut c = self.peek_char();
        let mut may_radix = 1;
        let radix = c.map_or(10, |c| if c == 'x' {16} else if c == 'o' {8} else if c == 'b' {2} else {10});

        loop {
            match c {
                Some('x') | Some('o') | Some('b') if may_radix > 0 => {self.expect_char()?;},
                Some(c) if c.is_digit(radix) => {self.expect_char()?;},
                Some('_')                    => {self.expect_char()?;},
                Some('.')                    => {
                    let res = self.make_token(if float { |s| TokenType::Floating(s) } else { |s| TokenType::Integer(s) }, offset);
                    let o = self.current_char_pos;
                    self.current_char_pos -= 1;
                    self.expect_char()?;

                    match self.peek_char() {
                        Some('.') => {
                            self.expect_char()?;
                            if let Some('=') = self.peek_char() {
                                self.expect_char()?;
                            }
                            let token = self.make_token(|s| TokenType::Operator(s), o);
                            self.cache.push(token);
                            return Ok(res);
                        }
                        _ if float && !exp   => return self.err("second ."),
                        _ if exp_float       => return self.err("second . after exponential"),
                        _ if !exp            => float = true,
                        _                    => {float = true; exp_float = true; self.expect_char()?;}
                    }
                },
                Some('-') if just_exp > 0    => {float = true; self.expect_char()?;},
                Some('+') if just_exp > 0    => {self.expect_char()?;},
                Some('e') if exp             => return self.err("second e, where there should be no exponential"),
                Some('e')                    => {exp = true; self.expect_char()?; just_exp=2; may_radix = 2;},
                _ => return Ok(self.make_token(if float { |s| TokenType::Floating(s) } else { |s| TokenType::Integer(s) }, offset)),
            };

            if may_radix > 0 {
                may_radix -= 1;
            }

            if just_exp > 0 {
                just_exp -= 1;
            }

            c = self.peek_char();
        }
    }

    pub fn peek(&mut self) -> Option<LexResult<'a>> {
        let val = self.next();
        if let Some(Ok(tok)) = &val {
            self.cache.push(tok.clone());
        }
        val
    }

    fn err(&self, static_: &'static str) -> LexResult<'a> {
        Err((String::from(static_), self.get_pos()))
    }
}

/*0x_a.e-o6.5*/


impl<'a> Iterator for Scanner<'a> {
    type Item = LexResult<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut skip = true;
        let mut inline_comment = false;
        let mut multiline_comment = false;
        let mut result = None;

        
        if let Some(val) = self.cache.pop() {
            let val = val.clone();
            return Some(Ok(val));
        }
        

        while skip {
            let o = self.current_char_pos;
            let c = self.next_char()?;

            if inline_comment {
                if c == '\n' {
                    self.new_line();
                    self.current_char_pos+=1;
                    inline_comment = false;
                }
                continue;
            }

            if multiline_comment {
                if c == '\n' {
                    self.new_line();
                }

                if c == '=' {
                    match self.next_char() {
                        Some('#') | Some('') => multiline_comment = false,
                        _ => ()
                    }
                    self.current_char_pos += 1;
                }
                continue;
            }

            skip = false;
            result = Some(match c {
                '\\' | 'λ' => Ok(self.make_token(|_| TokenType::Lambda, o)),
                ';' | ';' => Ok(self.make_token(|_| TokenType::Semicolon, o)),
                '(' | '（' => Ok(self.make_token(|_| TokenType::ParenLeft, o)),
                ')' | '）' => Ok(self.make_token(|_| TokenType::ParenRight, o)),
                '[' => Ok(self.make_token(|_| TokenType::BrackLeft, o)),
                ']' => Ok(self.make_token(|_| TokenType::BrackRight, o)),
                '{' => Ok(self.make_token(|_| TokenType::CurlyLeft, o)),
                '}' => Ok(self.make_token(|_| TokenType::CurlyRight, o)),
                '#' | '' => {
                    match self.peek_char() {
                        Some('#') | Some('') | Some('!') => {inline_comment = true; skip = true; self.err("unhandeled comment")},
                        Some(c) if c.is_alphanumeric() => {self.next_char(); self.get_var(o)},
                        Some('=') | Some('≝') => {self.next_char(); multiline_comment = true; skip = true; Err((String::from("unhandeled multiline comment"), self.get_pos()))}
                        Some(_) | None => Err((String::from("Just a hashtag chillin, bro"), self.get_pos()))
                    }
                }
                '`' => Ok(self.make_token(|_| TokenType::Hyphen, o)),
                '\n' => {self.new_line(); self.current_char_pos+=1; skip = true; self.err("unhandeled newline")},
                c if c.is_whitespace() => {self.current_char_pos+=1;skip = true; self.err("unhandeled whitespace")},
                '\'' => self.get_char(o),
                '"' => self.get_string(o),
                c if c.is_digit(10) => self.get_number(o),
                c if c.is_alphabetic() => self.get_var(o),
                _ => self.get_op(o)
            });
        }

        result
    }
}

