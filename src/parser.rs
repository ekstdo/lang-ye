use std::{str::CharIndices, iter::Peekable, collections::HashMap};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TokenType {
    ParenLeft, ParenRight, // ()
    BrackLeft, BrackRight, // []
    CurlyLeft, CurlyRight, // {}

    Integer, Floating, Char, Str,

    Operator, Assign, Reassign, Semicolon, Variable, Hyphen, // +, ;, a, `
    Lambda,

    If, Else, While, Let, For, Raw, Mut, Is, Return, Continue, Break,
    Ref, In, Static, Export, Import, Lazy, Async,

    Tag
}

#[derive(Debug, Clone,PartialEq)]
pub struct Token<'a> {
    pub type_: TokenType,
    pub line: usize,
    pub position: usize,
    pub slice: &'a str
}

impl TokenType {
    fn is_atom(&self) -> bool {
        use TokenType::*;
        match self {
            Integer | Floating | Char | Str | Variable => true,
            _ => false 
        }
    }

    fn is_lparen(&self) -> bool {
        use TokenType::*;
        match self {
            ParenLeft | BrackLeft | CurlyLeft => true,
            _ => false 
        }
    }

    fn is_rparen(&self) -> bool {
        use TokenType::*;
        match self {
            ParenRight | BrackRight | CurlyRight => true,
            _ => false 
        }
    }

}

pub type LexErr = (String, (usize, usize));
pub type LexResult<'a> = Result<Token<'a>, LexErr>;
#[derive(Debug, PartialEq)]
pub enum ParseErr<'a> {
    LexErr(LexErr),
    ParseErr(String, Token<'a>)
}

pub type ParseResult<'a> = Result<AST<'a>, ParseErr<'a>>;

fn escapeable(c: char) -> bool {
    c == 'n' || c == 't' || c == 'w' || c == 'b' || c == 'f' || c == 'v' || c == '0' || c == 'r'
}


pub struct Scanner<'a> {
    current_line: usize,
    current_line_pos: usize,
    iterator: Peekable<CharIndices<'a>>,
    string: &'a String,
    current_char_pos: usize,
    current_char_size: usize,
    cache: Vec<Token<'a>>
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

    fn var_match(s: &'a str) -> TokenType {
        if s.starts_with('#') {
            return TokenType::Tag;
        }
        match s {
            "let" => TokenType::Let,
            "if" => TokenType::If,
            "else" => TokenType::Else,
            "while" => TokenType::While,
            "for" => TokenType::For,
            "raw" => TokenType::Raw,
            "mut" => TokenType::Mut,
            "return" => TokenType::Return,
            "continue" => TokenType::Continue,
            "break" => TokenType::Break,
            "ref" => TokenType::Ref,
            "is" => TokenType::Is,
            "in" => TokenType::In,
            "static" => TokenType::Static,
            "export" => TokenType::Export,
            "import" => TokenType::Import,
            "lazy" => TokenType::Lazy,
            "async" => TokenType::Async,
            _ => TokenType::Variable
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
        self.next_char().ok_or((String::from("EOF ERROR"), self.get_pos()))
    }

    fn peek_char(&mut self) -> Option<char> {
        self.iterator.peek().map(|x| x.1)
    }

    fn new_line(&mut self) {
        self.current_line_pos = 0;
        self.current_line += 1;
    }

    fn make_token(&mut self, type_: TokenType, offset: usize) -> Token<'a> {
        let res = Token {
            type_,
            position: self.current_line_pos,
            line: self.current_line,
            slice: &self.string[offset..=self.current_char_pos + self.current_char_size - 1] };
        self.current_char_pos += 1;
        return res;
    }

    fn get_pos(&self) -> (usize, usize) {
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
                Ok(self.make_token(TokenType::Char, offset))
            } else {
                Err(e)
            }

        } else if self.expect_char()? == '\'' {
            Ok(self.make_token(TokenType::Char, offset))
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
        Ok(self.make_token(TokenType::Str, offset))
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
                    let slice = &self.string[offset..=self.current_char_pos + self.current_char_size - 1];
                    return Ok(self.make_token(Scanner::var_match(slice), offset))
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
                    return Ok(self.make_token(if slice == "=" || slice == "≔" {TokenType::Assign} else if slice.ends_with('=') {TokenType::Reassign} else {TokenType::Operator}, offset))
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
                    let res = self.make_token(if float { TokenType::Floating } else { TokenType::Integer }, offset);
                    let o = self.current_char_pos;
                    self.current_char_pos -= 1;
                    self.expect_char()?;

                    match self.peek_char() {
                        Some('.') => {
                            self.expect_char()?;
                            if let Some('=') = self.peek_char() {
                                self.expect_char()?;
                            }
                            let token = self.make_token(TokenType::Operator, o);
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
                _ => return Ok(self.make_token(if float { TokenType::Floating } else { TokenType::Integer }, offset)),
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
                '\\' | 'λ' => Ok(self.make_token(TokenType::Lambda, o)),
                ';' | ';' => Ok(self.make_token(TokenType::Semicolon, o)),
                '(' | '（' => Ok(self.make_token(TokenType::ParenLeft, o)),
                ')' | '）' => Ok(self.make_token(TokenType::ParenRight, o)),
                '[' => Ok(self.make_token(TokenType::BrackLeft, o)),
                ']' => Ok(self.make_token(TokenType::BrackRight, o)),
                '{' => Ok(self.make_token(TokenType::CurlyLeft, o)),
                '}' => Ok(self.make_token(TokenType::CurlyRight, o)),
                '#' | '' => {
                    match self.peek_char() {
                        Some('#') | Some('') | Some('!') => {inline_comment = true; skip = true; self.err("unhandeled comment")},
                        Some(c) if c.is_alphanumeric() => {self.next_char(); self.get_var(o)},
                        Some('=') | Some('≝') => {self.next_char(); multiline_comment = true; skip = true; Err((String::from("unhandeled multiline comment"), self.get_pos()))}
                        Some(_) | None => Err((String::from("Just a hashtag chillin, bro"), self.get_pos()))
                    }
                }
                '`' => Ok(self.make_token(TokenType::Hyphen, o)),
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

#[derive(Debug, Clone, PartialEq)]
pub enum InnerForLoop<'a> {
    In(AST<'a>, AST<'a>),
    Old(AST<'a>, AST<'a>, AST<'a>)
}

impl<'a> std::fmt::Display for InnerForLoop<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InnerForLoop::In(var, iter) => write!(f, "{} in {}", var, iter),
            InnerForLoop::Old(init, cond, step) => write!(f, "(init: {}; cond: {}; step: {})", init, cond, step),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum OperatorType {
    Infix, Prefix, Postfix
}

#[derive(Debug, Clone, PartialEq)]
pub enum ASTType<'a, T> {
    Unit,
    Empty,
    Integer(i32),
    Floating,
    Bool,
    Char(char),
    Variable(&'a str),
    Generated(String),
    OpVariable(&'a str, OperatorType),
    Str(&'a str),
    InfixOp(&'a str, Vec<T>),
    InfixSndOp(&'a str, T),
    PrefixOp(&'a str, T),
    PostfixOp(&'a str, T),
    Application(Vec<T>),
    Let(Vec<(T, Option<T>, bool, bool)>), // static, mut
    List(Vec<T>),
    Lambda(Vec<T>, T),
    While(T, T),
    If(T, T, Option<T>, bool), // has ending else
    For(InnerForLoop<'a>, T, Option<T>),
    Match(Vec<(T, T)>),
    Block(Vec<T>),
    TagStatement(&'a str, Vec<T>),
}

impl<'a, T> ASTType<'a, T> {
    fn needs_semicolon(&self) -> bool {
        match self {
            ASTType::While(_, _) | ASTType::For(_, _, _) | ASTType::Block(_) => false,
            ASTType::If(_, _, _, ending_else) => *ending_else,
            _ => true
        }
    }
}

impl<'a> std::fmt::Display for ASTType<'a, AST<'a>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ASTType::Integer(i) => write!(f, "Integer {}", i),
            ASTType::Floating => write!(f, "Floating"),
            ASTType::Str(s) => write!(f, "String {:?}", s),
            ASTType::Char(c) => write!(f, "Char {:?}", c),
            ASTType::Bool => write!(f, "Bool"),
            ASTType::InfixOp(op, ops) => {
                write!(f, "('{}': ", op)?;
                let mut first = true;
                for i in ops {
                    if first {
                        write!(f, "{}", i)?;
                    } else {
                        write!(f, ", {}", i)?;
                    }
                    first = false;
                }
                write!(f, ")")
            },
            ASTType::List(els) => {
                write!(f, "[")?;
                let mut first = true;
                for i in els {
                    if first {
                        write!(f, "{}", i)?;
                    } else {
                        write!(f, ", {}", i)?;
                    }
                    first = false;
                }
                write!(f, "]")
            }
            ASTType::Block(els) => {
                write!(f, "{{\n")?;
                let mut first = true;
                for i in els {
                    if first {
                        write!(f, "{}\n", i)?;
                    } else {
                        write!(f, ", {}", i)?;
                    }
                    first = false;
                }
                write!(f, "}}")
            }
            ASTType::Application(vals) => {write!(f, "(apply")?; vals.into_iter().for_each(|el| {write!(f, " {}", el);}); write!(f, ")")},
            ASTType::PrefixOp(op, ast) => write!(f, "({}: {})", op, ast),
            ASTType::Let(v) => {
                write!(f, "Let [")?;
                let mut first = true;
                for i in v {
                    match i {
                        (l, None, a, b) =>
                            if first {
                                write!(f, "{}{}{}", if *a {"mut "} else {""}, if *b {"static "} else {""}, l)?;
                            } else {
                                write!(f, ", {}{}{}", if *a {"mut "} else {""}, if *b {"static "} else {""}, l)?;
                            }
                        (l, Some(r), a, b) =>
                            if first {
                                write!(f, "{}{}{} = {}", if *a {"mut "} else {""}, if *b {"static "} else {""}, l, r)?;
                            } else {
                                write!(f, ", {}{}{} = {}", if *a {"mut "} else {""}, if *b {"static "} else {""}, l, r)?;
                            }
                    }
                    first = false;
                }
                write!(f, "]")
            }
            ASTType::If(cond, body, els, ending_else) => {
                write!(f, "If{} ({}) ({})", if *ending_else {"*"} else {""}, cond, body)?;
                match els {
                    None => Ok(()),
                    Some(x) => write!(f, " else ({})", x)
                }
            }
            ASTType::For(inner, body, els) => {
                write!(f, "For {} {}", inner, body)?;
                match els {
                    None => Ok(()),
                    Some(x) => write!(f, " else ({})", x)
                }
            }
            ASTType::Lambda(varlist, body) => {
                write!(f, "λ[")?;
                let mut first = true;
                for i in varlist {
                    if first {
                        write!(f, "{}", i)?;
                    } else {
                        write!(f, ", {}", i)?;
                    }
                    first = false;
                }
                write!(f, "] -> {}", body)

            }
            res => write!(f, "{:?}", res)
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct AST<'a> {
    pub pos_marker: Token<'a>,
    pub asttype: Box<ASTType<'a, AST<'a>>>
}

impl<'a> std::fmt::Display for AST<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.asttype.fmt(f)
    }
}

const APPLICATION_LEVEL: usize = 40;

pub struct Parser<'a> {
    pub infix_op: HashMap<String, (usize, usize)>,
    pub prefix_op: HashMap<String, usize>,
    pub postfix_op: HashMap<String, usize>,
    pub scanner: Scanner<'a>,
}

#[derive(PartialEq, Debug, Copy, Clone)]
enum Environment {
    InParen, InCondition, Nothing
}

impl<'a> Parser<'a> {
    pub fn new(scanner: Scanner<'a>) -> Parser<'a> {
        let infix_op = HashMap::from([
            (String::from(","), (5, 6)),    
            (String::from("=>"), (7, 8)),
            (String::from("="), (8, 7)),
            (String::from("|"), (10, 9)),
            (String::from("<-"), (11, 12)),   // backpassing

            (String::from("in"), (15, 9)),

            (String::from("<|"), (10, 9)),   // low prec operator
            (String::from("<||"), (10, 9)),  // uncurry
            (String::from("<|||"), (10, 9)), // uncurry2
            (String::from(">>="), (11, 12)),  // monad chain
            (String::from("|>"), (13, 14)),  // pipe
            (String::from("||>"), (13, 14)), // uncurry pipe
            (String::from("|||>"), (13, 14)),// uncurry2 pipe
            (String::from(":"), (15, 16)),  // type / casting
            (String::from("->"), (16, 15)), // function type operator
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
        Parser {infix_op , prefix_op, postfix_op, scanner}
    }

    fn make_atom(atype: ASTType<'a, AST<'a>>, token: Token<'a>) -> AST<'a> {
        AST { pos_marker: token, asttype: Box::new(atype)}
    }

    pub fn handle_error(&mut self, lines: &Vec<&'a str>, err: ParseErr){
        match err {
            ParseErr::LexErr((msg, (line, pos))) => {
                eprintln!("\x1b[1;38mLEX ERROR\x1b[0;38m at line {}", line + 1);
                eprintln!("    {}", lines[line]);
                eprintln!("    {: <1$}", "^", pos);
                eprintln!("{}", msg);
            },
            ParseErr::ParseErr(msg, token) => {
                eprintln!("\x1b[1;38mPARSE ERROR\x1b[0;38m at line {}", token.line + 1);
                eprintln!("    {}", lines[token.line]);
                eprintln!("    {: <1$}^", "", token.position);
                eprintln!("at token: {:?}", token);
                eprintln!("{}", msg);
            }
        }

        while let Some(tok) = self.scanner.next() {
            match tok {
                Ok(Token { type_: TokenType::Semicolon, .. }) => break,
                Ok(_) => continue,
                Err((msg, (line, pos))) => {
                    eprintln!("\x1b[1;38mLEX ERROR\x1b[0;38m at line {}", line + 1);
                    eprintln!("    {}", lines[line]);
                    eprintln!("    {: <1$}", "^", pos);
                    eprintln!("{}", msg);
                },
            }
        }


    }

    pub fn expect(&mut self, ttype: TokenType) -> Result<Token<'a>, ParseErr<'a>> {
        let tok = self.scanner.next().ok_or(ParseErr::LexErr((String::from("Expected token"), self.scanner.get_pos())))?.map_err(ParseErr::LexErr)?;
        if tok.type_ == ttype {
            Ok(tok)
        } else {
            Err(ParseErr::ParseErr(format!("Expected tokentype {:?}", ttype), tok))
        }
    }

    pub fn parse_tag(&mut self, tag: Token<'a>) -> ParseResult<'a> {
        self.scanner.next();
        match tag.slice {
            "#infix" => {
                let op = self.expect(TokenType::Operator)?;
                let lprec = self.expect(TokenType::Integer)?;
                let lprec = lprec.slice.parse::<usize>().map_err(|_| self.err("Couldn't parse integer", lprec))?;
                let rprec = self.expect(TokenType::Integer)?;
                let rprec = rprec.slice.parse::<usize>().map_err(|_| self.err("Couldn't parse integer", rprec))?;
                self.infix_op.insert(op.slice.to_string(), (lprec, rprec));
                Ok(Parser::make_atom(ASTType::Unit, op))
            }
            "#prefix"  => {
                let op = self.expect(TokenType::Operator)?;
                let lprec = self.expect(TokenType::Integer)?;
                let lprec = lprec.slice.parse::<usize>().map_err(|_| self.err("Couldn't parse integer", lprec))?;
                self.prefix_op.insert(op.slice.to_string(), lprec);
                Ok(Parser::make_atom(ASTType::Unit, op))
            }
            "#postfix"  => {
                let op = self.expect(TokenType::Operator)?;
                let lprec = self.expect(TokenType::Integer)?;
                let lprec = lprec.slice.parse::<usize>().map_err(|_| self.err("Couldn't parse integer", lprec))?;
                self.postfix_op.insert(op.slice.to_string(), lprec);
                Ok(Parser::make_atom(ASTType::Unit, op))
            }
            _ => todo!()
        }
    }

    fn parse(&mut self, peeked: Token<'a>, expect_semicolon: bool) -> ParseResult<'a> {
        let res = match peeked.type_ {
            TokenType::Let => self.parse_let(peeked, Environment::Nothing),
            TokenType::Tag => self.parse_tag(peeked),
            _ => self.parse_expr(0, Environment::Nothing)
        }?;
        if expect_semicolon {
            let needs_semicolon = res.asttype.needs_semicolon();
            if needs_semicolon {
                self.expect(TokenType::Semicolon)?;
            } else {
                let next = match self.scanner.peek() {
                    Some(n) => n, 
                    None => return Ok(res)
                }.map_err(ParseErr::LexErr)?;
                if next.type_ == TokenType::Semicolon {
                    self.next();
                }
            }
        }
        Ok(res)
    }

    fn parse_let(&mut self, peeked: Token<'a>, env: Environment) -> ParseResult<'a> {
        let mut mutable = false;
        let mut static_ = false;
        let mut vec = Vec::new();
        let mut expr = true;
        self.scanner.next();
        loop {
            let res = self.peek_token_or("Unfinished Let statement", &peeked)?;
            if res.type_ == TokenType::Mut && !mutable {
                mutable = true; 
                self.scanner.next();
            } else if res.type_ == TokenType::Static && !static_ {
                static_ = true;
                self.scanner.next();
            } else if res.type_ == TokenType::Semicolon && env != Environment::InCondition
                   || res.type_ == TokenType::CurlyLeft && env == Environment::InCondition {
                break;
            } else if expr {
                let mut el = self.parse_expr(6, env)?;
                let mut help_vec = Vec::new();
                while let AST { asttype: box ASTType::InfixOp("=", v), .. } = el {
                    let v = v.clone();
                    help_vec.push(v[0].clone());
                    el = v[1].clone();
                }
                help_vec.push(el);

                for i in (0..(help_vec.len() - 1).max(1)).rev() {
                    vec.push((help_vec[i].clone(), help_vec.get(i + 1).map(|x| x.clone()), mutable, static_));
                }

                expr = false;
            }

            if res.slice == "," {
                self.scanner.next();
                expr = true;
                mutable = false;
                static_ = false;
            }
        }
        Ok(Parser::make_atom(ASTType::Let(vec), peeked))
    }

    pub fn parse_atom_paren(&mut self, at: Token<'a>) -> ParseResult<'a> {
        let tok = self.peek_token_or("Unclosed (", &at)?;

        if self.infix_op.contains_key(tok.slice) {
            self.scanner.next();
            let tok2 = self.peek_token_or("Unclosed (", &at)?;
            if self.prefix_op.contains_key(tok.slice) {
                if tok2.type_== TokenType::ParenRight {
                    self.expect(TokenType::ParenRight)?;
                    Ok(Parser::make_atom(ASTType::OpVariable(tok.slice, OperatorType::Infix), tok))
                } else {
                    self.scanner.cache.push(tok);
                    let mut res = self.parse_expr(0, Environment::InParen);
                    self.expect(TokenType::ParenRight)?;
                    if let Ok(ast) = &mut res {
                        ast.pos_marker = at;
                    }
                    res
                }
            } else {
                let rprec = self.infix_op.get(tok.slice).unwrap().1;
                let rhs = self.parse_expr(rprec, Environment::InParen)?;
                self.expect(TokenType::ParenRight)?;
                Ok(Parser::make_atom(ASTType::InfixSndOp(tok.slice, rhs), tok))
            }
        } else {
            let mut res = self.parse_expr(0, Environment::InParen);
            self.expect(TokenType::ParenRight)?;
            if let Ok(ast) = &mut res {
                ast.pos_marker = at;
            }
            res
        }
    }

    fn parse_block(&mut self, at: Token<'a>) -> ParseResult<'a> {
        let mut next_token = self.peek_token_or("Unclosed Block", &at)?;
        let mut body = Vec::new();
        loop {
            let stmt = self.parse(next_token, false)?;
            body.push(stmt);
            next_token = self.peek_token_or("Unclosed Block", &at)?;
            if next_token.type_ == TokenType::CurlyRight {
                self.scanner.next();
                break;
            } else if next_token.type_ == TokenType::Semicolon {
                self.scanner.next();
            } else {
                return Err(self.err("unknown closing token", at));
            }

            next_token = self.peek_token_or("Unclosed Block", &at)?;
            if next_token.type_ == TokenType::CurlyRight {
                body.push(Parser::make_atom(ASTType::Unit, next_token));
                self.scanner.next();
                break;
            }
        }

        Ok(Parser::make_atom(ASTType::Block(body), at))
    }

    fn parse_for(&mut self, at: Token<'a>) -> ParseResult<'a> {
        let tok = self.peek_token_or("You either need \"(init, cond, step)\" or \"iden in iter\"", &at)?;
        let inner = if tok.type_ == TokenType::ParenLeft {
            self.scanner.next();
            let tok = self.peek_token_or("Atom needed in \"(\x1b[1;38minit\x1b[0;38m, cond, step)\"", &at)?;
            let init = self.parse(tok, true)?;
            let tok = self.peek_token_or("Atom needed in \"(init, \x1b[1;38mcond\x1b[0;38m, step)\"", &at)?;
            let cond = self.parse(tok, true)?;
            let tok = self.peek_token_or("Atom needed in\"(init, cond, \x1b[1;38mstep\x1b[0;38m)\"", &at)?;
            let step = self.parse(tok, false)?;
            self.expect(TokenType::ParenRight)?;
            InnerForLoop::Old(init, cond, step)
        } else {
            let cond = self.parse_expr(7, Environment::InCondition)?;

            match &*cond.asttype {
                ASTType::InfixOp("in", v) => InnerForLoop::In(v[0].clone(), v[1].clone()),
                _ => return Err(self.err("You either need \"(init, cond, step)\" or \"iden in iter\"", at))
            }
        };
        let tok = self.expect(TokenType::CurlyLeft)?;
        let body = self.parse_block(tok)?;


        let tok = match self.scanner.peek() {
            Some(t) => t.map_err(ParseErr::LexErr)?,
            None => {
                return Ok(Parser::make_atom(ASTType::For(inner, body, None), at));
            }
        };

        let res = if tok.type_ == TokenType::Else {
            self.scanner.next();
            let tok = self.peek_token_or("Unfinished else branch", &at)?;
            self.expect(TokenType::CurlyLeft)?;
            Some(self.parse_block(tok)?)
            
        } else { None };

        Ok(Parser::make_atom(ASTType::For(inner, body, res), at))
    }

    fn parse_while(&mut self, at: Token<'a>) -> ParseResult<'a> {
        let tok = self.peek_token_or("Condition needed after while", &at)?;
        let cond = if tok.type_ == TokenType::Let {
            self.parse_let(tok, Environment::InCondition)?
        } else {
            self.parse_expr(7, Environment::InCondition)?
        };
        let tok = self.expect(TokenType::CurlyLeft)?;
        let body = self.parse_block(tok)?;
        Ok(Parser::make_atom(ASTType::While(cond, body), at))
    }

    fn parse_if(&mut self, at: Token<'a>) -> ParseResult<'a> {
        let tok = self.peek_token_or("Condition neeeded after if", &at)?;
        let cond = if tok.type_ == TokenType::Let {
            self.parse_let(tok, Environment::InCondition)?
        } else {
            self.parse_expr(7, Environment::InCondition)?
        };
        let tok = self.expect(TokenType::CurlyLeft)?;
        let body = self.parse_block(tok)?;


        let tok = match self.scanner.peek() {
            Some(t) => t.map_err(ParseErr::LexErr)?,
            None => return Ok(Parser::make_atom(ASTType::If(cond, body, None, false), at))
        };

        let mut ending_else = false;


        let res = if tok.type_ == TokenType::Else {
            self.scanner.next();
            let tok = self.peek_token_or("Unfinished else branch", &at)?;
            Some(if tok.type_ == TokenType::If {
                self.scanner.next();
                let res = self.parse_if(tok)?;
                match *res.asttype {
                    ASTType::If(_, _, _, b) => ending_else = b,
                    _ => ()
                }
                res
            } else {
                self.expect(TokenType::CurlyLeft)?;
                ending_else = true;
                self.parse_block(tok)?
            })
        } else { None };

        Ok(Parser::make_atom(ASTType::If(cond, body, res, ending_else), at))
    }

    fn parse_expr(&mut self, level: usize, env: Environment) -> ParseResult<'a> {
        let next_token = self.scanner.next()
            .ok_or(ParseErr::LexErr((String::from("Expected token in this expession"), self.scanner.get_pos())))?
            .map_err(ParseErr::LexErr)?;

        // parsing the left hand side of a potential operation
        let mut lhs = match next_token {
            at if at.type_.is_atom() => self.parse_atom(at),
            Token { type_ : TokenType::ParenLeft, .. } => self.parse_atom_paren(next_token),
            Token { type_ : TokenType::BrackLeft, .. } => {
                let tok = self.peek_token_or("Unclosed [", &next_token)?;
                let res = self.parse_expr(0, Environment::Nothing);
                self.expect(TokenType::BrackRight)?;
                match res {
                    Ok(AST { asttype: box ASTType::InfixOp(",", vec), ..}) => Ok(Parser::make_atom(ASTType::List(vec), tok)),
                    Ok(inner) => Ok(Parser::make_atom(ASTType::List(vec![inner]), tok)),
                    Err(_) => res
                }
            }

            Token { type_ : TokenType::Operator, .. } => {
                let prec = *self.prefix_op.get(next_token.slice).ok_or(self.err("Operator is not a prefix operator", next_token.clone()))?;
                let res = self.parse_expr(prec, Environment::Nothing)?;
                Ok(Parser::make_atom(ASTType::PrefixOp(next_token.slice, res), next_token))
            },

            Token { type_ : TokenType::Lambda, .. } => {
                let lhs = self.parse_expr(18, Environment::Nothing)?;
                if self.expect(TokenType::Operator)?.slice != "->" {
                    return Err(self.err("expected -> in lambda expression", next_token))
                }
                let rhs = self.parse_expr(8, Environment::Nothing)?;
                let mut vars = Vec::new();

                if let ASTType::Application(varlist) = *lhs.asttype {
                    vars = varlist;
                } else {
                    vars.push(lhs);
                }
                return Ok(Parser::make_atom(ASTType::Lambda(vars, rhs), next_token));
            }

            Token { type_ : TokenType::For, .. } => return self.parse_for(next_token),
            Token { type_ : TokenType::While, .. } => return self.parse_while(next_token),
            Token { type_ : TokenType::If, .. } => {
                let res = self.parse_if(next_token)?;
                match *res.asttype {
                    ASTType::If(_, _, _, false) => return Ok(res),
                    _ => {}
                }
                Ok(res)
            }
            at => Err(self.err("Expected Atom Token", at))
        }?;

        loop {
            // checking for next operator
            let tok = match self.scanner.peek() {
                None => break,
                Some(tok) => tok
            };

            let op = match tok {
                Err(x) => return Err(ParseErr::LexErr(x)),
                Ok(sem) if sem.type_ == TokenType::Semicolon && env != Environment::InCondition
                        || sem.type_.is_rparen()
                        || env == Environment::InCondition && sem.type_ == TokenType::CurlyLeft
                       => break,
                Ok(x) => x
            }.clone();
            let op_str = op.slice;

            // function application in SML Style
            if op.type_.is_atom() || op.type_.is_lparen() {
                let prec = APPLICATION_LEVEL;
                if prec < level {
                    break;
                }

                let rhs = self.parse_expr(APPLICATION_LEVEL + 1, env)?;

                match &mut *lhs.asttype {
                    ASTType::Application(ap) => ap.push(rhs),
                    _ => lhs = Parser::make_atom(ASTType::Application(vec![lhs, rhs]), op)
                }
                continue;
            }

            // expecting certain Tokentypes
            if op.type_ != TokenType::Operator && op.type_ != TokenType::In && op.type_ != TokenType::Reassign  && op.type_ != TokenType::Assign{
                return Err(self.err("expected operator", op));
            }

            // postfix operators?
            if let Some(prec) = self.postfix_op.get(op.slice) {
                let prec = *prec;
                if prec < level {
                    break;
                }

                lhs = Parser::make_atom(ASTType::PostfixOp(op_str, lhs), op);
                continue;
            };

            // infix operator
            let (lp, rp) = match self.infix_op.get(op.slice) {
                Some((l, r)) => (*l, *r),
                None => return Err(self.err("unknown precedence of operator", op))
            };

            // stopping when stuff like: 1 * 2 + 3 happens
            if lp < level {
                break;
            }

            // consuming the infix operator
            self.scanner.next();

            // enabling stuff like (1/) <$> [1..5]
            if env == Environment::InParen { 
                let tok = self.peek_token_or("unclosed (", &op)?;
                if tok.type_ == TokenType::ParenRight {
                    lhs = Parser::make_atom(ASTType::InfixOp(op_str, vec![lhs]), op);
                    break;
                }
            }

            // parsing the righthand side of the infix operator
            let rhs = self.parse_expr(rp, env)?;

            // make comma seperated stuff to a list instead of nested AST
            if let AST { asttype: box ASTType::InfixOp(",", vec), pos_marker } = &mut lhs {
                if pos_marker.type_.is_lparen() {
                    lhs = Parser::make_atom(ASTType::InfixOp(op_str, vec![lhs, rhs]), op);
                } else {
                    vec.push(rhs);
                }
            } else {
                lhs = Parser::make_atom(ASTType::InfixOp(op_str, vec![lhs, rhs]), op);
            }
        }

        Ok(lhs)
    }

    fn parse_atom(&self, token: Token<'a>) -> ParseResult<'a> {
        match token {
            Token { type_: TokenType::Integer, .. } => Ok(Parser::make_atom(
                    ASTType::Integer(token.slice.parse::<i32>().map_err(|_| self.err("Could not parse integer", token.clone()))?),
                    token)),
            Token { type_: TokenType::Floating, .. } => Ok(Parser::make_atom(ASTType::Floating, token)),
            Token { type_: TokenType::Char, .. } => Ok(Parser::make_atom(ASTType::Char(token.slice.chars().collect::<Vec<_>>()[1]), token)),
            Token { type_: TokenType::Str, .. } => Ok(Parser::make_atom(ASTType::Str(&token.slice[1..token.slice.len() - 1]), token)),
            Token { type_: TokenType::Variable, .. } => Ok(Parser::make_atom(ASTType::Variable(token.slice), token)),
            _ => Err(self.err("expected other token while atomizing", token))
        }
    }

    fn err(&self, static_: &'static str, token: Token<'a>) -> ParseErr<'a> {
        ParseErr::ParseErr(String::from(static_), token)
    }

    fn peek_token_or(&mut self, msg: &'static str, at: &Token<'a>) -> Result<Token<'a>, ParseErr<'a>> {
        self.scanner.peek().ok_or(self.err(msg, at.clone()))?.map_err(ParseErr::LexErr)
    }
}

impl<'a> Iterator for Parser<'a> {
    type Item = ParseResult<'a>;
    
    fn next(&mut self) -> Option<Self::Item> {
        let peeked = match self.scanner.peek()? {
            Ok(a) => a,
            Err(e) => return Some(Err(ParseErr::LexErr(e)))
        };
        Some(self.parse(peeked, true))
    }
}

pub struct Desugarer {
    counter: usize
}

impl Desugarer {
    pub fn new() -> Self {
        Desugarer { counter: 0 }
    }

    pub fn desugar<'a>(&mut self, ast: AST<'a>) -> AST<'a> {
        let AST { pos_marker, asttype: ttype } = ast;
        match *ttype {
            ASTType::For(InnerForLoop::In(var, iter), block, els) => unimplemented!(),
            ASTType::InfixOp(op, mut vec) => {
                let opvar = AST { pos_marker: pos_marker.clone(), asttype: Box::new(ASTType::OpVariable(op, OperatorType::Infix)) };
                vec = vec.into_iter().map(|x| self.desugar(x)).collect();
                vec.insert(0, opvar);
                AST {pos_marker, asttype: Box::new(ASTType::Application(vec))}
            }
            ASTType::InfixSndOp(op, operand)  => {
                let temp_var = AST {pos_marker: pos_marker.clone(), asttype: Box::new(ASTType::Generated( { self.counter += 1; format!("a{}", self.counter) } ))};
                AST {pos_marker: pos_marker.clone(), asttype: Box::new(ASTType::Lambda(vec![
                    temp_var.clone()
                ], AST {pos_marker: pos_marker.clone(), asttype: Box::new(ASTType::Application(vec![
                    AST {pos_marker: pos_marker.clone(), asttype: Box::new(ASTType::OpVariable(pos_marker.slice, OperatorType::Infix))},
                    temp_var,
                    operand
                ])) }))}
            }
            ASTType::Application(v) => {
                AST {pos_marker, asttype: Box::new(ASTType::Application(v.into_iter().map(|x| self.desugar(x)).collect()))}
            }
            ASTType::Let(v) => 
                AST {pos_marker, asttype: Box::new(ASTType::Let(
                            v.into_iter().map( |(x, v, s, m)|
                                (x, v.map(|x| self.desugar(x)), s, m)
                            ).collect()
                        ))},
            x => AST {pos_marker, asttype: Box::new(x)}
        }
    }

}

#[cfg(test)]
mod test {
    use super::*;

    fn assert_parsed(text: &'static str, to_match: &'static str){
        let text = String::from(text);
        let mut parser = Parser::new(Scanner::new(&text));
        assert_eq!(format!("{}", parser.next().unwrap().unwrap().asttype), String::from(to_match))
    }

    #[test]
    fn test_empty_file(){
        let text = String::from("");
        let scanner = Scanner::new(&text);
        let mut parser = Parser::new(scanner);

        assert_eq!(parser.next(), None);
    }

    #[test]
    fn test_custom_infix_operator(){
        let text = String::from("##defining your own custom operators\n\
                    #infix <<>> 10 9;\n\
                    a <<>> b;");
        let scanner = Scanner::new(&text);
        let mut parser = Parser::new(scanner);

        assert_eq!(*parser.next().unwrap().unwrap().asttype, ASTType::Unit);
        assert_eq!(format!("{}", parser.next().unwrap().unwrap().asttype), String::from("('<<>>': Variable(\"a\"), Variable(\"b\"))"))
    }

    #[test]
    fn test_sml_syntax(){
        let text = "f 1 3 + f 2 - 5;";
        let to_match = "('-': ('+': (apply (apply Variable(\"f\") Integer 1) Integer 3), (apply Variable(\"f\") Integer 2)), Integer 5)";

        assert_parsed(text, to_match)
    }

    #[test]
    fn test_lambda(){
        let text = "\\x -> x + 5;";
        let to_match = "λ[Variable(\"x\")] -> ('+': Variable(\"x\"), Integer 5)";

        assert_parsed(text, to_match)
    }
}
