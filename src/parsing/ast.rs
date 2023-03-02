use num_bigint::BigInt;

#[derive(Debug)]
pub enum ForAST<'a> {
    Old(Option<ExprAST<'a>>, Option<ExprAST<'a>>, Option<ExprAST<'a>>),
    In(ExprAST<'a>, ExprAST<'a>)
}

#[derive(Debug)]
pub enum StmtAST<'a> {
    Expr(ExprAST<'a>),
    If(ExprAST<'a>, Box<StmtAST<'a>>),
    IfElse(ExprAST<'a>, Box<StmtAST<'a>>, Box<StmtAST<'a>>),
    Block(Vec<StmtAST<'a>>),
    While(ExprAST<'a>, Box<StmtAST<'a>>),
    For(ForAST<'a>, Box<StmtAST<'a>>),
    Let(Vec<ExprAST<'a>>),
}

#[derive(Debug)]
pub enum ExprAST<'a> {
    Int(BigInt),
    Float(f64),
    Char(char),
    String(&'a str),
    Var(&'a str, bool, bool),
    Op(&'a str),
    Tuple(Vec<ExprAST<'a>>),
    List(Vec<ExprAST<'a>>),
    Appl(Vec<ExprAST<'a>>),
    Lambda(Vec<ExprAST<'a>>, Box<ExprAST<'a>>),
    Assign(Box<ExprAST<'a>>, Box<ExprAST<'a>>),
    IfElse(Box<ExprAST<'a>>, Box<ExprAST<'a>>, Box<ExprAST<'a>>),
    Block(Vec<StmtAST<'a>>, Box<ExprAST<'a>>),
    Void,
    Paren(Box<ExprAST<'a>>),
    Match(Vec<(ExprAST<'a>, ExprAST<'a>)>)
}
