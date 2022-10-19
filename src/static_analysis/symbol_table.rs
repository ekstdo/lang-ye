

use std::collections::HashMap;
use core::hash::Hash;

use crate::parsing::parser::{AST, ASTType};

use super::typing::Type;

pub struct SymbolTable<A, B> where A: PartialEq + Eq + Hash {
    inner: Vec<HashMap<A, B>>
}

impl<A, B> SymbolTable<A, B> where A: PartialEq + Eq + Hash {
    pub fn new() -> Self {
        Self { inner: vec![HashMap::new()] }
    }

    pub fn push_scope(&mut self) {
        self.inner.push(HashMap::new())
    }

    pub fn pop_scope(&mut self) -> Option<HashMap<A, B>> {
        self.inner.pop()
    }

    pub fn read(&self, a: &A) -> Option<&B> {
        self.inner.iter().rev().fold(None, |acc: Option<&B>, x: &HashMap<A, B>| acc.or(x.get(a)))
    }

    pub fn push(&mut self, a: A, b: B) {
        match self.inner.last_mut() {
            Some(map) => { map.insert(a, b) ; }
            None => self.push_scope()
        }
    }

    pub fn overwrite(&mut self, a: A, b: B) -> Result<(), ()> {
        for map in self.inner.iter_mut().rev() {
            match map.get(&a) {
                Some(_entry) => {
                    map.insert(a, b);
                    return Ok(());
                }
                None => {
                    continue;
                }
            }
        }
        return Err(())
    }

    pub fn overwrite_current_scope(&mut self, a: A, b: B) -> Result<(), ()> {
        let map =  self.inner.last_mut().ok_or(())?;
        map.get(&a).ok_or(())?;
        map.insert(a, b);
        Ok(())
    }
}

pub struct VarInformation<'a> {
    pub static_: bool,
    pub mut_ : bool,
    pub type_: Type<'a>,
    pub name: &'a str
}

impl <'a> SymbolTable<&'a str, VarInformation<'a>>  {
    pub fn scan_scope(&mut self, a: &AST) {
        match &*a.asttype {
            ASTType::Let(v) => {
                for (vars, vals) in v {
                }
                todo!("Let not scannable")
            }
            _ => {
                // do nothing
            }
        }
    }
}





