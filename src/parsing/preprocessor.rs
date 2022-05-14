
type Node = usize;

pub struct DFA {
    transitions: Vec<Vec<Node>>,
    finals: HashSet<Node>,
}

impl DFA {
    pub fn transition(&self, letter: usize, state: usize) -> Node {
        self.transitions[letter][state]
    }

    pub fn is_final(&self, state: Node) -> bool {
        self.finals.contains(&state)
    }

    pub fn run(&self, mut state: Node, tape: Vec<usize>) -> Node {
        for i in tape {
            state = self.transition(i, state);
        }

        state
    }
}

pub struct NFA {
    transitions: Vec<Vec<HashSet<Node>>>,
    finals: HashSet<Node>,
    epsilons: Vec<HashSet<Node>>
}

impl NFA {
    pub fn transition(&self, letter: usize, state: usize) -> HashSet<Node> {
        self.transitions[letter][state].clone()
    }

    pub fn is_final(&self, state: &HashSet<Node>) -> bool {
        !self.finals.is_disjoint(state)
    }

    pub fn run(&self, state: Node, tape: Vec<usize>) -> HashSet<Node> {
        let mut states = HashSet::from([state]);
        for i in tape {
            states = states.into_iter().map(|x| self.transition(i, x)).flatten().collect();
        }

        states
    }
}

enum NDState {
    Single(Node),
    Multiple(HashSet<Node>)
}

impl Into<DFA> for NFA {
    fn into(self) -> DFA {
        let translator: HashMap<NDState, Node> = HashMap::new();

        todo!()
    }
}

struct Preprocessor {
}

/*
 *
 * #macro reee ( ( ${elements:identifier} $, )* ${last:identifier} ) = { ## a is Vec<Identifier>
 *  let block = lit! { { let result = Set.new(); } };
 *  for el in elements {
 *    block.block_append(lit! { result.insert($el) });
 *  }
 *  block.block_append(lit! { result });
 *  block
 * }
 *
 *
 *
 *
 *
 *
 */

use std::collections::{HashSet, HashMap};
