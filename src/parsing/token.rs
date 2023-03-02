
pub type Spanned<Tok, Loc, Error> = Result<(Loc, Tok, Loc), Error>;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Token<'input> {
    ParenLeft, ParenRight, // ()
    BrackLeft, BrackRight, // []
    CurlyLeft, CurlyRight, // {}

    Integer(&'input str), Floating(&'input str), Char(char), String(&'input str),

    Operator(&'input str), Assign, Reassign(&'input str), Semicolon, Variable(&'input str), Hyphen, // +, ;, a, `
    Lambda, Comma, To, Matches,

    If, Else, While, Let, For, Raw, Mut, Is, Return, Continue, Break,
    Ref, In, Static, Export, Import, Lazy, Async, Await,

    Tag(&'input str), Goto, Here
}
