use crate::parsing::parser::{self, ASTType, AST};
use crate::parsing::token;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq)]
pub struct Trait<'a> {
    name: &'a str,
    applied: Vec<Type<'a>>,
}

impl<'a> Trait<'a> {
    fn replace(self, from: usize, to: &Type<'a>) -> Trait<'a> {
        Trait {
            applied: self.applied.into_iter().map(|x| x.replace(from, to)).collect(),
            name: self.name
        }
    }

    fn contains_str(&self, has: &'a str) -> bool {
        self.applied.iter().map(|x| x.contains_str(has)).any(|x| x)
    }

    fn contains(&self, has: usize) -> bool {
        self.applied.iter().map(|x| x.contains(has)).any(|x| x)
    }

    fn free_vars(&self) -> HashSet<usize> {
        let mut res = HashSet::new();
        self.applied.iter().for_each(|el| res.extend(&el.free_vars()));
        res
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type<'a> {
    Single(&'a str),
    Application(&'a str, Vec<Type<'a>>),
    Var(&'a str, usize),
    Polymorphic(HashSet<usize>, Vec<Trait<'a>>, Box<Type<'a>>)
}

impl<'a> Type<'a> {
    fn free_vars(&self) -> HashSet<usize> {
        match self {
            Type::Single(_) => HashSet::new(),
            Type::Application(_, vals) => {
                let mut res = HashSet::new();
                vals.iter().for_each(|el| res.extend(&el.free_vars()));
                res
            },
            Type::Var(v, u) => HashSet::from([*u]),
            Type::Polymorphic(bound, traits, type_) => {
                let mut res = type_.free_vars();
                traits.iter().for_each(|el| res.extend(el.free_vars()));
                res
            }
        }
    }

    fn contains_str(&self, has: &'a str) -> bool {
        match self {
            Type::Var(s, u) => &has == s,
            Type::Single(_) => false,
            Type::Application(v, appl) => appl.iter().map(|x| x.contains_str(has)).any(|x| x),
            Type::Polymorphic(v, traits, typ) => {
                traits.iter().map(|x| x.contains_str(has)).any(|x| x) || typ.contains_str(has) 
            }
        }
    }

    fn contains(&self, has: usize) -> bool {
        match self {
            Type::Var(s, u) => &has == u,
            Type::Single(_) => false,
            Type::Application(v, appl) => appl.iter().map(|x| x.contains(has)).any(|x| x),
            Type::Polymorphic(v, traits, typ) => {
                traits.iter().map(|x| x.contains(has)).any(|x| x) || typ.contains(has) 
            }
        }
    }

    // warning: This function doesn't do ANY CHECKS, it just repleaces stuff!!!
    fn replace(self, from: usize, to: &Type<'a>) -> Type<'a> {
        match self {
            Type::Var(s, u) if u == from => to.clone(),
            Type::Var(s, u) => Type::Var(s, u),
            Type::Single(_) => self.clone(),
            Type::Application(s, ap) => Type::Application(s, ap.into_iter().map(|x| x.replace(from, to)).collect()),
            Type::Polymorphic(mut s, traits, typ) => {
                let new_traits = traits.into_iter().filter(|x| x.free_vars() != HashSet::from([from])).collect();
                if s == HashSet::from([from]) {
                    typ.replace(from, to)
                } else {
                    s.retain(|x| x != &from);
                    Type::Polymorphic(s, new_traits, Box::new(typ.replace(from, to)))
                }
            }
        }
    }
}

// let f: Functor (Box x) => 

#[derive(Debug, Clone, PartialEq)]
pub struct TypedAST<'a> {
    pub pos_marker: token::Token<'a>,
    pub asttype: Box<ASTType<'a, TypedAST<'a>>>,
    pub type_: Type<'a>
}

const integral_trait: &'static str = "Integral";
const i32_type_name: &'static str = "I32";
const string_type_name: &'static str = "String";
const unit_type_name: &'static str = "Unit";

type TypeError<'a> = (String, TypedAST<'a>, Type<'a>); // message, current, expected
type TypingResult<'a> = Result<TypedAST<'a>, TypeError<'a>>;

struct Typer<'a> {
    trait_impls: HashMap<Trait<'a>, Vec<Vec<Type<'a>>>>,
    typed_vars: Vec<HashMap<&'a str, Type<'a>>>,
    type_counter: usize
}


// Vec I32 a b , Vec I32 I32 String

fn unify<'a>(should: &Type<'a>,
             is: &Type<'a>,
             unifyable: &mut HashMap<usize, Option<Type<'a>>>,
             restrictions: &mut Vec<Trait<'a>>) -> bool {
    match (should, is) {
        _ if should == is => true,
        (Type::Var(s, u), _) => {
            match unifyable.get(u) {
                None => todo!(),
                Some(None) => {
                    let is_free = is.free_vars();
                    for i in is_free {
                        if !unifyable.contains_key(&i) {
                            unifyable.insert(i, None);
                        }
                    }
                    unifyable.insert(*u, Some(is.clone()));
                    true
                },
                Some(Some(t)) => unify(&t.clone(), is, unifyable, restrictions),
            }
        },
        (Type::Application(a1, v1), Type::Application(a2, v2)) => {
            if a1 == a2 {
                v1.iter().zip(v2).all(|(x1, x2)| unify(x1, x2, unifyable, restrictions))
            } else {
                false
            }
        }
        _ => false
    }
}


impl<'a> Typer<'a> {
    fn new() -> Self {
        Typer { trait_impls: HashMap::new(), typed_vars: Vec::new(), type_counter: 0 }
    }

    fn type_ast(&mut self, ast: parser::AST<'a>) -> TypingResult<'a> {
        let AST { pos_marker, box asttype } = ast;
        let (type_, new_asttype) = match asttype {
            ASTType::Integer(i) => (Type::Single(i32_type_name), ASTType::Integer(i)),
            ASTType::Str(s) => (Type::Single(string_type_name), ASTType::Str(s)),
            ASTType::Unit => (Type::Single(unit_type_name), ASTType::Unit),
            ASTType::Variable(v) => match self.typed_vars.iter().rev().map(|x| x.get(v)).fold(None,|acc, el| acc.or(el)) {
                Some(type_) => (type_.clone(), ASTType::Variable(v)),
                None => return Err(("undeclared variable".to_string(), TypedAST { pos_marker, asttype: Box::new(ASTType::Variable(v)), type_: Type::Single(unit_type_name) }, Type::Single(unit_type_name)))
            }
            ASTType::Application(vecs) => {
                let vecs = vecs.iter()
                    .map(|x| self.type_ast(x.clone()))
                    .collect::<Result<Vec<TypedAST<'a>>, TypeError<'a>>>()?;
                let mut unifyable = HashMap::new();
                let mut restrictions = Vec::new();
                let len = vecs.len();
                let mut fn_type = Type::Var("gen", self.type_counter);
                unifyable.insert(self.type_counter, None);
                self.type_counter += 1;
                for _ in 0..len - 1 {
                    fn_type = Type::Application("->", vec![Type::Var("gen", self.type_counter), fn_type]);
                    unifyable.insert(self.type_counter, None);
                    self.type_counter += 1;
                }
                
                unify(&fn_type, &vecs[0].type_, &mut unifyable, &mut restrictions);

                println!("{:?}", unifyable);

                todo!()
            }
            _ => todo!()
        };
        Ok(TypedAST { pos_marker, asttype: Box::new(new_asttype), type_ })
    }
}




#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    #[test]
    fn test_replace() {
        // eg. the type signature for id:
        let hash_types = HashSet::from([0]);
        let type_ = Type::Polymorphic(hash_types.clone(),
                                        Vec::new(),
                                        Box::new(Type::Application("->", vec![Type::Var("a", 0), Type::Var("a", 0)])));

        println!("{:?}", type_.replace(0, &Type::Single("I32")));

        // eg. the type signature for add:
        let type_ = Type::Polymorphic(hash_types.clone(), vec![Trait { name: "Add", applied: vec![Type::Var("a", 0)] }], Box::new(Type::Application("->", vec![Type::Var("a", 0), Type::Application("->", vec![Type::Var("a", 0), Type::Var("a", 0)])])));

        println!("{:?}", type_.replace(0, &Type::Single("I32")));
    }

    #[test]
    fn typing(){

        let to_type = "f 1;";

        let mut typer = Typer::new();
        let scope = HashMap::from([("f", Type::Application("->", vec![Type::Single("I32"), Type::Single("I32")]))]);
        typer.typed_vars.push(scope);
        
        typer.type_ast(Parser::from_string(&to_type.to_string()).next().unwrap().unwrap());
    }

    #[test]
    fn test_unify(){
        let mut unifyable = HashMap::new();
        unifyable.insert(0, None);
        let res = unify(&Type::Application("Vec", vec![Type::Var("a", 0)]),
              &Type::Application("Vec", vec![Type::Single("I32")]), &mut unifyable, &mut Vec::new());

        println!("Result1: {}, unified: {:?}", res, unifyable);


        unifyable.insert(0, None);
        let res = unify(&Type::Application("Vec", vec![Type::Var("a", 0)]),
              &Type::Application("Vec", vec![Type::Application("Vec", vec![Type::Single("I32")])]), &mut unifyable, &mut Vec::new());

        println!("Result2: {}, unified: {:?}", res, unifyable);

        unifyable.insert(0, None);
        let res = unify(&Type::Application("Vec", vec![Type::Var("a", 0)]),
              &Type::Application("Vec", vec![Type::Application("Vec", vec![Type::Var("b", 1)])]), &mut unifyable, &mut Vec::new());

        println!("Result: {}, unified: {:?}", res, unifyable);

        unifyable.insert(0, None);
        unifyable.remove(&1);
        let res = unify(&Type::Application("->", vec![Type::Application("Vec", vec![Type::Var("a", 0)]), Type::Application("Vec", vec![Type::Var("a", 0)])]),
              &Type::Application("->", vec![
                                 Type::Application("Vec", vec![Type::Application("Vec", vec![Type::Var("b", 1)]) ]),
                                 Type::Application("Vec", vec![Type::Application("Vec", vec![Type::Single("I32")]) ]) ]), &mut unifyable, &mut Vec::new());

        println!("Result3: {}, unified: {:?}", res, unifyable);


        unifyable.insert(0, None);
        unifyable.insert(1, None);
        let res = unify(&Type::Application(
                "->", vec![Type::Var("a", 0), Type::Application("->", vec![Type::Var("b", 1)]), Type::Application("Vec", vec![Type::Var("a", 0)])]),
            &Type::Application(
                "->", vec![Type::Var("c", 2), Type::Var("d", 3)]), &mut unifyable, &mut vec![]);

        println!("Result4: {}, unified: {:?}", res, unifyable);

        unifyable.insert(2, None);
        unifyable.insert(3, None);
        let res = unify(&Type::Application(
                "->", vec![Type::Var("c", 2), Type::Var("d", 3)]),
                &Type::Application(
                "->", vec![Type::Var("a", 0), Type::Application("->", vec![Type::Var("b", 1), Type::Var("b", 1)]), Type::Application("Vec", vec![Type::Var("a", 0)])]), &mut unifyable, &mut vec![]);

        println!("Result5: {}, unified: {:?}", res, unifyable);

    }
}
