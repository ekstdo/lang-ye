
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Token<'input> {
    ParenLeft, ParenRight, // ()
    BrackLeft, BrackRight, // []
    CurlyLeft, CurlyRight, // {}

    Integer(&'input str), Floating(&'input str), Char(char), Str(&'input str),

    Operator(&'input str), Assign, Reassign(&'input str), Semicolon, Variable(&'input str), Hyphen, // +, ;, a, `
    Lambda,

    If, Else, While, Let, For, Raw, Mut, Is, Return, Continue, Break,
    Ref, In, Static, Export, Import, Lazy, Async, Await,

    Tag, Goto, Here
}

impl Token {
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


