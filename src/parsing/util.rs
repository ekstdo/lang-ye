use num_bigint::BigInt;

use super::ast::ExprAST;

pub fn parse_balanced_ternary<'input>(s: &'input str) -> BigInt {
    let mut accum = BigInt::from_bytes_be(num_bigint::Sign::Plus ,&[0u8]);
    for i in s.chars() {
        accum *= 3usize;
        match i {
            '-' => accum -= 1isize,
            '0' => (),
            '1' => accum += 1isize,
            _ => todo!()
        }
    }
    return accum;
}

pub fn parse_int<'input>(s: &'input str) -> BigInt {
    let radix = s.get(1..2);
    let mut r: isize = 10;
    if let Some("x") = radix { // hex numbers can't have exponents, 
                                     // because e is a hex digit 
        return BigInt::parse_bytes(s.as_bytes(), 16).unwrap();
    } else if let Some("o") = radix {
        r = 8;
    } else if let Some("b") = radix {
        r = 2;
    } else if let Some("t") = radix {
        r = 3;
    } else if let Some("⚖") = s.get(1..4){
        r =  -3;
    }
    let mut spliter = s.split("e");
    let l = spliter.next().unwrap();
    match spliter.next() {
        Some(r) => parse_int(&(String::from("0") + &String::from(r))),
        None if r == -3 => parse_balanced_ternary(l.get(4..).unwrap()),
        None => BigInt::parse_bytes(l.as_bytes(), r as u32).unwrap()
    }
}


pub fn parse_float<'a>(s: &'a str) -> f64 {
    0.0
}

pub fn appl<'a>(mut l: Vec<ExprAST<'a>>) -> ExprAST<'a> {
    if l.len() == 1 {
        l.pop().unwrap()
    } else {
        ExprAST::Appl(l)
    }
}
