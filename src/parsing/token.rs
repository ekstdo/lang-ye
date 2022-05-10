
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
    pub fn is_atom(&self) -> bool {
        use TokenType::*;
        match self {
            Integer | Floating | Char | Str | Variable => true,
            _ => false 
        }
    }

    pub fn is_lparen(&self) -> bool {
        use TokenType::*;
        match self {
            ParenLeft | BrackLeft | CurlyLeft => true,
            _ => false 
        }
    }

    pub fn is_rparen(&self) -> bool {
        use TokenType::*;
        match self {
            ParenRight | BrackRight | CurlyRight => true,
            _ => false 
        }
    }

}


