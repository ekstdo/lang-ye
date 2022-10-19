use crate::parsing::parser::{self, ASTType, AST};
use crate::parsing::token;
use std::collections::{HashMap, HashSet};


#[derive(Clone, Hash, PartialEq, Eq)]
enum Kind {
    Star,
    Fun(Box<Kind>, Box<Kind>)
}

impl std::fmt::Debug for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::Star => f.write_str("*"),
            Kind::Fun(box Kind::Star, b) => write!(f, "* -> {:?}", b),
            Kind::Fun(a, b) => write!(f, "({:?} -> {:?})", a, b)
        }
    }
}

type Id<'a> = &'a str;
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
enum TVType<'a> {
    Id(Id<'a>),
    Int(usize)
}
type TypeVar<'a> = (TVType<'a>, Kind);

#[derive(Debug, Clone, PartialEq, Eq)]
enum Type<'a> {
    Var(TypeVar<'a>),
    Con(Id<'a>, Kind),
    Ap(Box<Type<'a>>, Box<Type<'a>>),
    Gen(usize)
}

static tUnit: Type<'static> = Type::Con("()", Kind::Star);
static tChar: Type<'static> = Type::Con("Char", Kind::Star);
static tI32: Type<'static> = Type::Con("I32", Kind::Star);
static tF32: Type<'static> = Type::Con("F32", Kind::Star);
static tString: Type<'static> = Type::Con("String", Kind::Star);

fn tArrlist() -> Type<'static> {
    Type::Con("[]", Kind::Fun(Box::new(Kind::Star), Box::new(Kind::Star)))
}

fn tArrlistWrapper<'a>(t: Type<'a>) -> Type<'a> {
    Type::Ap(Box::new(tArrlist()), Box::new(t))
}

fn tArrow() -> Type<'static> {
    Type::Con("->", Kind::Fun(Box::new(Kind::Star), Box::new(Kind::Fun(Box::new(Kind::Star), Box::new(Kind::Star)))))
}

impl<'a> std::ops::Shr for Type<'a> {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self::Output {
        Type::Ap(Box::new(Type::Ap(Box::new(tArrow()), Box::new(self))), Box::new(rhs))
    }
}


impl<'a> Type<'a> {
    pub fn has_kind(&self) -> Result<&Kind, ()> {
        Ok(match self {
            Type::Var((_, k)) => k,
            Type::Con(_, k) => k,
            Type::Ap(box l, _) => match l.has_kind() {
                Ok(Kind::Fun(_, k)) => k,
                _ => return Err(())
            },
            Type::Gen(_) => todo!()
        })
    }

    pub fn var_bind(&self, var: TypeVar<'a>) -> Result<Subst<'a>, String> {
        if self == &Type::Var(var.clone()) {
            Ok(Subst(HashMap::new()))
        } else if self.tv().contains(&var) {
            Err("occurs check fails".to_string())
        } else if &var.1 != self.has_kind().unwrap() {
            Err("kinds do not match".to_string())
        } else {
            Ok(Subst(HashMap::from([(var, self.clone())])))
        }
    }

    pub fn mgu(&self, other: &Type<'a>) -> Result<Subst<'a>, String> {
        match (self, other) {
            (Type::Ap(l, r), Type::Ap(l_, r_)) => {
                let s1 = l.mgu(l_)?;
                let s2 = r.mgu(r_)?;

                Ok(&s1 * &s2)
            }
            (Type::Var(v), t) 
                | (t, Type::Var(v)) => t.var_bind(v.clone()),
            (Type::Con(t1, k1), Type::Con(t2, k2))
                if t1 == t2 && k1 == k2
                => Ok(Subst(HashMap::new())),

            _=> Err("types do not unify".to_string())
        }
    }

    pub fn match_(&self, right: &Type<'a>) -> Result<Subst<'a>, String> {
        match (self, right) {
            (Type::Ap(l, r), Type::Ap(l_, r_)) => {
                let sl = l.match_(l_)?;
                let sr = r.match_(r_)?;
                (sl + sr).ok_or("match failed".to_string())
            },
            (Type::Var(v), t) if &v.1 == t.has_kind().unwrap() =>
                Ok(Subst(HashMap::from([(v.clone(), t.clone())]))),
            (Type::Con(t1, k1), Type::Con(t2, k2)) if t1 == t2 && k1 == k2 =>
                Ok(Subst(HashMap::new())),
            _ => Err("types do not match".to_string())
        }
    }

    fn in_hnf(&self) -> bool {
        match self {
            Type::Var(_) => true,
            Type::Con(_, _) => false,
            Type::Ap(t, _) => t.in_hnf(),
            Type::Gen(_) => todo!()
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Subst<'a>(HashMap<TypeVar<'a>, Type<'a>>);


trait Typeable<'a> {
    fn apply(self, sub: &Subst<'a>) -> Self;
    fn tv(&self) -> HashSet<&TypeVar<'a>>;
}

impl<'a> Typeable<'a> for Type<'a> {
    fn apply(self, sub: &Subst<'a>) -> Self {
        match self {
            Type::Var(v) => sub.0.get(&v).map(Type::clone).unwrap_or(Type::Var(v)),
            Type::Ap(l, r) => Type::Ap(Box::new(l.apply(sub)), Box::new(r.apply(sub))),
            t => t
        }
    }

    fn tv(&self) -> HashSet<&TypeVar<'a>> {
        match self {
            Type::Var(v) => HashSet::from([v]),
            Type::Ap(l, r) => {
                let mut l = l.tv();
                l.extend(r.tv());
                l
            },
            _ => HashSet::new()
        }
    }
}

impl<'a, T: Typeable<'a>> Typeable<'a> for Vec<T> {
    fn apply(self, sub: &Subst<'a>) -> Self {
        self.into_iter().map(|x| x.apply(sub)).collect()
    }

    fn tv(&self) -> HashSet<&TypeVar<'a>> {
        self.iter().map(T::tv).flatten().collect()
    }
}

// implementation of @@
impl<'a> std::ops::Mul for &Subst<'a> {
    type Output = Subst<'a>;

    fn mul(self, rhs: Self) -> Self::Output {
        Subst(self
              .0
              .clone()
              .into_iter()
              .map(|(v, t)| (v, t.apply(&rhs)))
              .chain(rhs.0.clone())
              .collect())
    }
}

// implementation of merge
impl<'a> std::ops::Add for Subst<'a> {
    type Output = Option<Subst<'a>>;

    fn add(mut self, rhs: Self) -> Self::Output {
        for (key, i) in &self.0 {
            if rhs.0.contains_key(&key) && i.clone().apply(&self) != i.clone().apply(&rhs) {
                return None;
            }
        }

        self.0.extend(rhs.0);
        Some(self)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Qual<'a, T: Eq> {
    predicates: Vec<Pred<'a>>,
    t: T
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Pred<'a> (Id<'a>, Type<'a>);

impl<'a, T: Typeable<'a> + std::cmp::Eq> Typeable<'a> for Qual<'a, T> {
    fn apply(self, sub: &Subst<'a>) -> Self {
        Qual { predicates: self.predicates.apply(sub), t: self.t.apply(sub) }
    }

    fn tv(&self) -> HashSet<&TypeVar<'a>> {
        let mut a = self.predicates.tv();
        a.extend(self.t.tv());
        a
    }
}

impl <'a> Typeable<'a> for Pred<'a> {
    fn apply(self, sub: &Subst<'a>) -> Self {
        Pred (self.0, self.1.apply(sub))
    }

    fn tv(&self) -> HashSet<&TypeVar<'a>> {
        self.1.tv()
    }
}

impl <'a> Pred<'a> {
    fn in_hnf(&self) -> bool {
        self.1.in_hnf()
    }
}

fn lift<'a>(f: &dyn Fn(&Type<'a>, &Type<'a>) -> Pred<'a>, p1: Pred<'a>, p2: Pred<'a>) -> Result<Pred<'a>, String> {
    if p1.0 == p2.0 {
        Ok(f(&p1.1, &p2.1))
    } else {
        Err("classes differ".to_string())
    }
}

type Class<'a> = (Vec<Id<'a>>, Vec<Inst<'a>>);
type Inst<'a> = Qual<'a, Pred<'a>>;


#[derive(Debug)]
struct ClassEnv<'a> { 
    classes: HashMap<Id<'a>, Class<'a>>,
    defaults: Vec<Type<'a>>
}

// TODO: make an error enum for type inferece

impl<'a> ClassEnv<'a> {
    fn new() -> Self {
        ClassEnv { classes: HashMap::new(), defaults: [tI32.clone()].to_vec() }
    }
    fn super_(&self, id: Id<'a>) -> Option<&Vec<Id<'a>>> {
        self.classes.get(id).map(|(a, _b)| a)
    }

    fn insts(&self, id: Id<'a>) -> Option<&Vec<Inst<'a>>> {
        self.classes.get(id).map(|(_a, b)| b)
    }

    fn add_class(&mut self, id: Id<'a>, is: Vec<Id<'a>>) -> Result<(), String> {
        match self.classes.get(id) {
            Some(_) => Err("class already defined".to_string()),
            None if is.iter().any(|x| self.classes.get(x).is_none()) =>
                Err("superclass not defined".to_string()),
            _ => Ok({ self.classes.insert(id, (is, Vec::new())); })
        }
    }

    fn add_core_classes(&mut self) -> Result<(), String> {
        self.add_class("Eq", vec![])?;
        self.add_class("Ord", vec!["Eq"])?;
        Ok(())
    }

    fn add_inst(&mut self, ps: Vec<Pred<'a>>, p: Pred<'a>) -> Result<(), String> {
        self.classes.get(p.0).ok_or("no class for instance".to_string())?;
        if self.insts(p.0).unwrap().iter().map(|x| &x.predicates).flatten().any(|pred: &Pred<'a>| overlap(&p, &pred)) {
            return Err("overlapping instance".to_string());
        }
        self.classes.get_mut(p.0).unwrap().1.push(Qual { predicates: ps, t: p });
        Ok(())
    }

    fn add_example_insts(&mut self) -> Result<(), String> {
        self.add_inst(vec![], Pred ("Eq", tUnit.clone()))?;
        self.add_inst(vec![], Pred ("Ord", tUnit.clone()))?;

        Ok(())
    }

    fn by_super(&self, p: &Pred<'a>) -> Option<Vec<Pred<'a>>> {
        let mut v: Vec<Pred<'a>> = self.super_(p.0)?.iter().map(|x| Pred (x, p.1.clone())).collect();
        v.push(p.clone());
        Some(v)
    }

    fn by_inst(&self, p: &Pred<'a>) -> Result<Option<Vec<Pred<'a>>>, String> {
        for i in self.insts(p.0).ok_or("No instances for predicate".to_string())? {
            if let Ok(u) = i.t.1.match_(&p.1) {
                return Ok(Some(i.predicates.iter().map(|x| x.clone().apply(&u)).collect()));
            }
        }
        Ok(None)
    }

    fn entail(&self, preds: &Vec<Pred<'a>>, p: Pred<'a>) -> bool {
        (match preds.into_iter()
                .map(|x|self.by_super(x))
                .collect::<Option<Vec<_>>>() {
                    Some(x) => x.into_iter().any(|x| x.contains(&p)),
                    None => false
        }) || match self.by_inst(&p) {
            Err(_) | Ok(None) => false,
            Ok(Some(s)) => s.into_iter().all(|pn| self.entail(preds, pn))
        }
    }

    fn to_hnfs(&self, preds: Vec<Pred<'a>>) -> Result<Vec<Pred<'a>>, String> {
        preds
            .into_iter()
            .map(|x| self.to_hnf(x))
            .collect::<Result<Vec<_>, _>>()
            .map(|x|x.into_iter().flatten().collect())
    }

    fn to_hnf(&self, pred: Pred<'a>) -> Result<Vec<Pred<'a>>, String> {
        if pred.in_hnf() {
            return Ok(vec![pred]);
        }

        self.to_hnfs(self.by_inst(&pred)?.ok_or("context reduction error".to_string())?)
    }

    fn simplify(&self, preds: Vec<Pred<'a>>) -> Vec<Pred<'a>> {
        let mut res = Vec::new();

        for (index, i) in preds.iter().enumerate() {
            if !self.entail(&res.iter().chain(&preds[index + 1..]).cloned().collect(), i.clone()){
                res.push(i.clone());
            }
        }

        res
    }

    fn reduce(&self, preds: Vec<Pred<'a>>) -> Result<Vec<Pred<'a>>, String> {
        Ok(self.simplify(self.to_hnfs(preds)?))
    }
}

fn overlap<'a>(p: &Pred<'a>, q: &Pred<'a>) -> bool {
    p.1.mgu(&q.1).is_ok()
}

#[derive(Clone, Debug)]
struct Scheme<'a>(Vec<Kind>, Qual<'a, Type<'a>>);

impl<'a> Typeable<'a> for Scheme<'a> {
    fn apply(self, sub: &Subst<'a>) -> Self {
        Scheme (self.0, self.1.apply(sub))
    }

    fn tv(&self) -> HashSet<&TypeVar<'a>> {
        self.1.tv()
    }
}

impl<'a> Scheme<'a> {
    fn quantify(tvs: Vec<TypeVar<'a>>, qt: Qual<'a, Type<'a>>) -> Self {
        let vs : Vec<TypeVar<'a>> = qt
            .tv()
            .into_iter()
            .filter(|x| tvs.contains(x))
            .cloned()
            .collect();
        Self(
            vs.clone().into_iter().map(|x| x.1).collect(),
            qt.apply(
                &Subst(vs.into_iter().zip((1..).into_iter().map(Type::Gen)).collect::<HashMap<_, _>>())
            ))
    }
}

impl<'a> Into<Scheme<'a>> for Type<'a> {
    fn into(self) -> Scheme<'a> {
        Scheme(vec![], Qual { predicates: vec![], t: self})
    }
}

#[derive(Debug)]
struct Assumption<'a> (Id<'a>, Scheme<'a>);

impl<'a> Typeable<'a> for Assumption<'a> {
    fn apply(self, sub: &Subst<'a>) -> Self {
        Assumption(self.0, self.1.apply(sub))
    }

    fn tv(&self) -> HashSet<&TypeVar<'a>> {
        self.1.tv()
    }
}

fn find<'a>(id: Id<'a>, assump: &Vec<Assumption<'a>>) -> Result<Scheme<'a>, String> {
    for i in assump {
        if i.0 == id {
            return Ok(i.1.clone());
        }
    }
    Err(format!("unbound identifier {}", id))
}


pub struct TypeInfer<'a> {
    counter: usize,
    subst: Subst<'a>
}

impl <'a> TypeInfer<'a> {
    pub fn new() -> Self {
        TypeInfer { counter: 0, subst: Subst(HashMap::new()) }
    }

    fn ext_subst(&mut self, sub: &Subst<'a>){
        self.subst = &self.subst * sub;
    }

    fn unify(&mut self, t1: Type<'a>, t2: Type<'a>) -> Result<(), String> {
        let u = t1.apply(&self.subst).mgu(&t2.apply(&self.subst))?;
        Ok(self.ext_subst(&u))
    }

    fn new_type(&mut self, kind: Kind) -> Type<'a> {
        self.counter += 1;
        Type::Var((TVType::Int(self.counter), kind))
    }

    fn fresh_inst(&mut self, scheme: &Scheme<'a>) -> Qual<'a, Type<'a>> {
        let ts = scheme.0.iter().cloned().map(|x| self.new_type(x)).collect::<Vec<_>>();
        scheme.1.clone().inst(&ts)
    }

    fn infer_expr(&mut self, env: &ClassEnv<'a>, assumptions: &Vec<Assumption<'a>>, expr: &AST<'a>) -> Result<(Vec<Pred<'a>>, Type<'a>), String> {
        Ok(match &*expr.asttype {
            ASTType::Unit => (vec![], tUnit.clone()),
            ASTType::Integer(_) => {
                let v = self.new_type(Kind::Star);
                (vec![Pred("Num", v.clone())], v)
            },
            ASTType::Char(_) => (vec![], tChar.clone()),
            ASTType::Str(_) => (vec![], tString.clone()),

            ASTType::Variable(s) => {
                let sc = find(s, assumptions)?;
                let Qual { predicates, t } = self.fresh_inst(&sc);
                (predicates, t)
            },
            ASTType::Application(v) => {
                let (mut ls, mut tl) = self.infer_expr(env, assumptions, &v[0])?;
                for j in &v[1..] {
                    let (mut rs, tr) = self.infer_expr(env, assumptions, j)?;
                    let t = self.new_type(Kind::Star);

                    self.unify(tr >> t.clone(), tl)?; // direction matters for 
                    tl = t;
                    ls.append(&mut rs);
                }
                (ls, tl)
            }
            _ => todo!()
        })
    }

    fn infer_pattern(){}

    fn parse_type(ast: &AST<'a>) -> Result<Type<'a>, String>{
        match &*ast.asttype {
            ASTType::Unit => Ok(tUnit.clone()),
            _ => todo!()
        }
    }
}

trait Instable<'a> {
    fn inst(self, types: &Vec<Type<'a>>) -> Self;
}

impl<'a> Instable<'a> for Type<'a> {
    fn inst(self, types: &Vec<Type<'a>>) -> Self {
        match self {
            Type::Ap(x, y) => Type::Ap(Box::new(x.inst(types)), Box::new(y.inst(types))),
            Type::Gen(u) => types[u].clone(),
            t => t
        }
    }
}

impl <'a, T: Instable<'a> + Eq> Instable<'a> for Qual<'a, T> {
    fn inst(self, types: &Vec<Type<'a>>) -> Self {
        Qual { predicates: self.predicates.into_iter().map(|x| x.inst(types)).collect(), t: self.t.inst(types) }
    }
}

impl <'a> Instable<'a> for Pred<'a> {
    fn inst(self, types: &Vec<Type<'a>>) -> Self {
        Pred(self.0, self.1.inst(types))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    #[ignore]
    fn type_test(){
        assert_eq!(
                 tArrlistWrapper(Type::Var((TVType::Id("x"), Kind::Star)))
                 .match_(&tArrlistWrapper(tI32.clone())),
                 Ok(Subst(HashMap::from([((TVType::Id("x"), Kind::Star), (Type::Con("I32", Kind::Star)))]))))
    }

    #[test]
    #[ignore]
    fn insts_before_classes_test(){
        let mut cenv = ClassEnv::new();
        assert!(cenv.add_example_insts().is_err());
    }

    #[test]
    #[ignore]
    fn entail_test() -> Result<(), String> {
        let mut cenv = ClassEnv::new();
        cenv.add_core_classes()?;
        cenv.add_example_insts()?;

        assert!(cenv.entail(&vec![], Pred("Eq", tUnit.clone())));
        assert!(!cenv.entail(&vec![], Pred("Num", tUnit.clone())));

        Ok(())
    }

    #[test]
    #[ignore]
    fn reduce_none_pred_test() -> Result<(), String> {
        let mut cenv = ClassEnv::new();
        cenv.add_core_classes()?;

        assert!(cenv.reduce(vec![Pred("Eq", tUnit.clone()), Pred("Eq", tUnit.clone())]).is_err());
        Ok(())
    }

    #[test]
    #[ignore]
    fn reduce_zero_pred_test() -> Result<(), String> {
        let mut cenv = ClassEnv::new();
        cenv.add_core_classes()?;
        cenv.add_example_insts()?;

        assert_eq!(cenv.reduce(vec![Pred("Eq", tUnit.clone()), Pred("Eq", tUnit.clone())])?.len(), 0);
        Ok(())
    }

    #[test]
    #[ignore]
    fn reduce_some_pred_test() -> Result<(), String> {
        let mut cenv = ClassEnv::new();
        cenv.add_core_classes()?;
        cenv.add_example_insts()?;

        assert_eq!(cenv.reduce(vec![
            Pred("Eq", Type::Var((TVType::Id("a"), Kind::Star))),
            Pred("Eq", Type::Var((TVType::Id("a"), Kind::Star)))])?.len(), 1);
        Ok(())
    }

    use crate::parser::Parser;
    #[test]
    fn literal_inference() {
        let s = "'a';1;".to_string();
        let mut parser = Parser::from_string(&s);
        let mut tinf = TypeInfer::new();
        let mut cenv = ClassEnv::new();
        cenv.add_core_classes().unwrap();
        cenv.add_example_insts().unwrap();
        let assumptions = vec![];
        assert_eq!(
            tinf.infer_expr(&cenv, &assumptions, &parser.next().unwrap().unwrap()).unwrap(),
            (vec![], tChar.clone())
        );

        assert_eq!(
            tinf.infer_expr(&cenv, &assumptions, &parser.next().unwrap().unwrap()).unwrap(),
            (vec![Pred ("Num", Type::Var((TVType::Int(1), Kind::Star)))], Type::Var((TVType::Int(1), Kind::Star)))
        );
    }

    #[test]
    fn expr_inference() {
        let s = "addInt 1 2; add1 1;".to_string();
        let mut parser = Parser::from_string(&s);
        let mut tinf = TypeInfer::new();
        let mut cenv = ClassEnv::new();
        cenv.add_core_classes().unwrap();
        cenv.add_example_insts().unwrap();
        cenv.add_class("Num", vec![]).unwrap();
        let type_ = tinf.new_type(Kind::Star);
        let type2 = tinf.new_type(Kind::Star);
        let assumptions = vec![
            Assumption("addInt", Scheme(vec![], Qual {predicates: vec![Pred("Num", type_.clone())], t: type_.clone() >> (type_.clone() >> type_.clone()) })),
            Assumption("add1", Scheme(vec![], Qual {predicates: vec![Pred("Num", type2.clone())], t: type2.clone() >> type2.clone()}))
        ];
        println!("{:?}", assumptions);
        println!(
            "{:?}",
            tinf.infer_expr(&cenv, &assumptions, &parser.next().unwrap().unwrap()).unwrap()
        );
        println!("{:?}", tinf.subst);

        println!(
            "{:?}",
            tinf.infer_expr(&cenv, &assumptions, &parser.next().unwrap().unwrap()).unwrap()
        );
        println!("{:?}", tinf.subst);
    }
}

// #[derive(Debug, Clone, PartialEq)]
// pub struct Trait<'a> {
//     name: &'a str,
//     applied: Vec<Type<'a>>,
// }

// impl<'a> Trait<'a> {
//     fn replace(self, from: usize, to: &Type<'a>) -> Trait<'a> {
//         Trait {
//             applied: self.applied.into_iter().map(|x| x.replace(from, to)).collect(),
//             name: self.name
//         }
//     }

//     fn contains_str(&self, has: &'a str) -> bool {
//         self.applied.iter().map(|x| x.contains_str(has)).any(|x| x)
//     }

//     fn contains(&self, has: usize) -> bool {
//         self.applied.iter().map(|x| x.contains(has)).any(|x| x)
//     }

//     fn free_vars(&self) -> HashSet<usize> {
//         let mut res = HashSet::new();
//         self.applied.iter().for_each(|el| res.extend(&el.free_vars()));
//         res
//     }
// }

// #[derive(Debug, Clone, PartialEq)]
// pub enum Type<'a> {
//     Single(&'a str),
//     Application(&'a str, Vec<Type<'a>>),
//     Var(&'a str, usize),
//     Polymorphic(HashSet<usize>, Vec<Trait<'a>>, Box<Type<'a>>)
// }

// impl<'a> Type<'a> {
//     fn free_vars(&self) -> HashSet<usize> {
//         match self {
//             Type::Single(_) => HashSet::new(),
//             Type::Application(_, vals) => {
//                 let mut res = HashSet::new();
//                 vals.iter().for_each(|el| res.extend(&el.free_vars()));
//                 res
//             },
//             Type::Var(v, u) => HashSet::from([*u]),
//             Type::Polymorphic(bound, traits, type_) => {
//                 let mut res = type_.free_vars();
//                 traits.iter().for_each(|el| res.extend(el.free_vars()));
//                 res
//             }
//         }
//     }

//     fn contains_str(&self, has: &'a str) -> bool {
//         match self {
//             Type::Var(s, u) => &has == s,
//             Type::Single(_) => false,
//             Type::Application(v, appl) => appl.iter().map(|x| x.contains_str(has)).any(|x| x),
//             Type::Polymorphic(v, traits, typ) => {
//                 traits.iter().map(|x| x.contains_str(has)).any(|x| x) || typ.contains_str(has) 
//             }
//         }
//     }

//     fn contains(&self, has: usize) -> bool {
//         match self {
//             Type::Var(s, u) => &has == u,
//             Type::Single(_) => false,
//             Type::Application(v, appl) => appl.iter().map(|x| x.contains(has)).any(|x| x),
//             Type::Polymorphic(v, traits, typ) => {
//                 traits.iter().map(|x| x.contains(has)).any(|x| x) || typ.contains(has) 
//             }
//         }
//     }

//     // warning: This function doesn't do ANY CHECKS, it just repleaces stuff!!!
//     fn replace(self, from: usize, to: &Type<'a>) -> Type<'a> {
//         match self {
//             Type::Var(s, u) if u == from => to.clone(),
//             Type::Var(s, u) => Type::Var(s, u),
//             Type::Single(_) => self.clone(),
//             Type::Application(s, ap) => Type::Application(s, ap.into_iter().map(|x| x.replace(from, to)).collect()),
//             Type::Polymorphic(mut s, traits, typ) => {
//                 let new_traits = traits.into_iter().filter(|x| x.free_vars() != HashSet::from([from])).collect();
//                 if s == HashSet::from([from]) {
//                     typ.replace(from, to)
//                 } else {
//                     s.retain(|x| x != &from);
//                     Type::Polymorphic(s, new_traits, Box::new(typ.replace(from, to)))
//                 }
//             }
//         }
//     }
// }

// // let f: Functor (Box x) => 

// #[derive(Debug, Clone, PartialEq)]
// pub struct TypedAST<'a> {
//     pub pos_marker: token::Token<'a>,
//     pub asttype: Box<ASTType<'a, TypedAST<'a>>>,
//     pub type_: Type<'a>
// }

// const integral_trait: &'static str = "Integral";
// const i32_type_name: &'static str = "I32";
// const string_type_name: &'static str = "String";
// const unit_type_name: &'static str = "Unit";

// type TypeError<'a> = (String, TypedAST<'a>, Type<'a>); // message, current, expected
// type TypingResult<'a> = Result<TypedAST<'a>, TypeError<'a>>;

// struct Typer<'a> {
//     trait_impls: HashMap<Trait<'a>, Vec<Vec<Type<'a>>>>,
//     typed_vars: Vec<HashMap<&'a str, Type<'a>>>,
//     type_counter: usize
// }


// // Vec I32 a b , Vec I32 I32 String

// fn unify<'a>(should: &Type<'a>,
//              is: &Type<'a>,
//              unifyable: &mut HashMap<usize, Option<Type<'a>>>,
//              restrictions: &mut Vec<Trait<'a>>) -> bool {
//     match (should, is) {
//         _ if should == is => true,
//         (Type::Var(s, u), _) => {
//             match unifyable.get(u) {
//                 None => todo!(),
//                 Some(None) => {
//                     let is_free = is.free_vars();
//                     for i in is_free {
//                         if !unifyable.contains_key(&i) {
//                             unifyable.insert(i, None);
//                         }
//                     }
//                     unifyable.insert(*u, Some(is.clone()));
//                     true
//                 },
//                 Some(Some(t)) => unify(&t.clone(), is, unifyable, restrictions),
//             }
//         },
//         (Type::Application(a1, v1), Type::Application(a2, v2)) => {
//             if a1 == a2 {
//                 v1.iter().zip(v2).all(|(x1, x2)| unify(x1, x2, unifyable, restrictions))
//             } else {
//                 false
//             }
//         }
//         _ => false
//     }
// }


// impl<'a> Typer<'a> {
//     fn new() -> Self {
//         Typer { trait_impls: HashMap::new(), typed_vars: Vec::new(), type_counter: 0 }
//     }

//     fn type_ast(&mut self, ast: parser::AST<'a>) -> TypingResult<'a> {
//         let AST { pos_marker, box asttype } = ast;
//         let (type_, new_asttype) = match asttype {
//             ASTType::Integer(i) => (Type::Single(i32_type_name), ASTType::Integer(i)),
//             ASTType::Str(s) => (Type::Single(string_type_name), ASTType::Str(s)),
//             ASTType::Unit => (Type::Single(unit_type_name), ASTType::Unit),
//             ASTType::Variable(v) => match self.typed_vars.iter().rev().map(|x| x.get(v)).fold(None,|acc, el| acc.or(el)) {
//                 Some(type_) => (type_.clone(), ASTType::Variable(v)),
//                 None => return Err(("undeclared variable".to_string(), TypedAST { pos_marker, asttype: Box::new(ASTType::Variable(v)), type_: Type::Single(unit_type_name) }, Type::Single(unit_type_name)))
//             }
//             ASTType::Application(vecs) => {
//                 let vecs = vecs.iter()
//                     .map(|x| self.type_ast(x.clone()))
//                     .collect::<Result<Vec<TypedAST<'a>>, TypeError<'a>>>()?;
//                 let mut unifyable = HashMap::new();
//                 let mut restrictions = Vec::new();
//                 let len = vecs.len();
//                 let mut fn_type = Type::Var("gen", self.type_counter);
//                 unifyable.insert(self.type_counter, None);
//                 self.type_counter += 1;
//                 for _ in 0..len - 1 {
//                     fn_type = Type::Application("->", vec![Type::Var("gen", self.type_counter), fn_type]);
//                     unifyable.insert(self.type_counter, None);
//                     self.type_counter += 1;
//                 }
                
//                 unify(&fn_type, &vecs[0].type_, &mut unifyable, &mut restrictions);

//                 println!("{:?}", unifyable);

//                 todo!()
//             }
//             _ => todo!()
//         };
//         Ok(TypedAST { pos_marker, asttype: Box::new(new_asttype), type_ })
//     }
// }




// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::parser::Parser;

//     #[test]
//     fn test_replace() {
//         // eg. the type signature for id:
//         let hash_types = HashSet::from([0]);
//         let type_ = Type::Polymorphic(hash_types.clone(),
//                                         Vec::new(),
//                                         Box::new(Type::Application("->", vec![Type::Var("a", 0), Type::Var("a", 0)])));

//         println!("{:?}", type_.replace(0, &Type::Single("I32")));

//         // eg. the type signature for add:
//         let type_ = Type::Polymorphic(hash_types.clone(), vec![Trait { name: "Add", applied: vec![Type::Var("a", 0)] }], Box::new(Type::Application("->", vec![Type::Var("a", 0), Type::Application("->", vec![Type::Var("a", 0), Type::Var("a", 0)])])));

//         println!("{:?}", type_.replace(0, &Type::Single("I32")));
//     }

//     #[test]
//     fn typing(){

//         let to_type = "f 1;";

//         let mut typer = Typer::new();
//         let scope = HashMap::from([("f", Type::Application("->", vec![Type::Single("I32"), Type::Single("I32")]))]);
//         typer.typed_vars.push(scope);
        
//         typer.type_ast(Parser::from_string(&to_type.to_string()).next().unwrap().unwrap());
//     }

//     #[test]
//     fn test_unify(){
//         let mut unifyable = HashMap::new();
//         unifyable.insert(0, None);
//         let res = unify(&Type::Application("Vec", vec![Type::Var("a", 0)]),
//               &Type::Application("Vec", vec![Type::Single("I32")]), &mut unifyable, &mut Vec::new());

//         println!("Result1: {}, unified: {:?}", res, unifyable);


//         unifyable.insert(0, None);
//         let res = unify(&Type::Application("Vec", vec![Type::Var("a", 0)]),
//               &Type::Application("Vec", vec![Type::Application("Vec", vec![Type::Single("I32")])]), &mut unifyable, &mut Vec::new());

//         println!("Result2: {}, unified: {:?}", res, unifyable);

//         unifyable.insert(0, None);
//         let res = unify(&Type::Application("Vec", vec![Type::Var("a", 0)]),
//               &Type::Application("Vec", vec![Type::Application("Vec", vec![Type::Var("b", 1)])]), &mut unifyable, &mut Vec::new());

//         println!("Result: {}, unified: {:?}", res, unifyable);

//         unifyable.insert(0, None);
//         unifyable.remove(&1);
//         let res = unify(&Type::Application("->", vec![Type::Application("Vec", vec![Type::Var("a", 0)]), Type::Application("Vec", vec![Type::Var("a", 0)])]),
//               &Type::Application("->", vec![
//                                  Type::Application("Vec", vec![Type::Application("Vec", vec![Type::Var("b", 1)]) ]),
//                                  Type::Application("Vec", vec![Type::Application("Vec", vec![Type::Single("I32")]) ]) ]), &mut unifyable, &mut Vec::new());

//         println!("Result3: {}, unified: {:?}", res, unifyable);


//         unifyable.insert(0, None);
//         unifyable.insert(1, None);
//         let res = unify(&Type::Application(
//                 "->", vec![Type::Var("a", 0), Type::Application("->", vec![Type::Var("b", 1)]), Type::Application("Vec", vec![Type::Var("a", 0)])]),
//             &Type::Application(
//                 "->", vec![Type::Var("c", 2), Type::Var("d", 3)]), &mut unifyable, &mut vec![]);

//         println!("Result4: {}, unified: {:?}", res, unifyable);

//         unifyable.insert(2, None);
//         unifyable.insert(3, None);
//         let res = unify(&Type::Application(
//                 "->", vec![Type::Var("c", 2), Type::Var("d", 3)]),
//                 &Type::Application(
//                 "->", vec![Type::Var("a", 0), Type::Application("->", vec![Type::Var("b", 1), Type::Var("b", 1)]), Type::Application("Vec", vec![Type::Var("a", 0)])]), &mut unifyable, &mut vec![]);

//         println!("Result5: {}, unified: {:?}", res, unifyable);

//     }
// }
