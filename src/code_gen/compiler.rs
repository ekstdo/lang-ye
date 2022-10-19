use crate::parser::{ASTType, AST, OperatorType};
use crate::vm::chunk::{Chunk, OpCode};

pub struct Compiler {
    pub globals: std::collections::HashMap<String, u32>,
    pub next_global_pos: u32
}

impl Compiler {
    pub fn new() -> Self {
        Self { globals: std::collections::HashMap::new(), next_global_pos: 0 }
    }

    pub fn compile<'a>(&mut self, chunk: &mut Chunk, ast: &AST<'a>) -> Result<(), &'static str> {
        match &*ast.asttype {
            ASTType::Integer(i) => {
                chunk.write_code(OpCode::Int, ast.pos_marker.line as u32);
                let pos = chunk.add_int(*i);
                chunk.write_value(pos as u32, 4, ast.pos_marker.line as u32);
                self.next_global_pos += 4;
            },
            ASTType::Str(s) => {
                chunk.write_code(OpCode::Int, ast.pos_marker.line as u32);
                let pos = chunk.add_int(s.len() as i32);
                chunk.write_value(pos as u32, 4, ast.pos_marker.line as u32);
                chunk.write_code(OpCode::Ref, ast.pos_marker.line as u32);
                let pos = chunk.add_slice(s.as_bytes());
                chunk.write_value(pos as u32, 4, ast.pos_marker.line as u32);
                self.next_global_pos += 8;
            }
            ASTType::Variable(s) => {
                match self.globals.get(&s.to_string()) {
                    None => todo!("Variable not in global scope"),
                    Some(v) => {
                        chunk.write_code(OpCode::GetGlobal, ast.pos_marker.line as u32);
                        chunk.write_value(*v, 4, ast.pos_marker.line as u32)
                    }
                }
                self.next_global_pos += 4;
            }
            ASTType::Let(v) => {
                for (var, val) in v {
                    match *var.asttype {
                        ASTType::Variable(v) => {
                            self.globals.insert(v.to_string(), self.next_global_pos);
                            println!("Globals: {:?}", self.globals);
                            match val {
                                Some(val) => self.compile(chunk, val)?,
                                None => chunk.write_code(OpCode::DefineGlobal, var.pos_marker.line as u32)
                            }
                        },
                        _ => todo!("dunno how to handle pattern matching yet, lol")
                    }
                }
            }
            ASTType::Application(vec) => {
                match &*vec[0].asttype {
                    ASTType::OpVariable("+", OperatorType::Infix) => {
                        self.compile(chunk, vec.get(1).ok_or("Expected argument 1")?)?;
                        self.compile(chunk, vec.get(2).ok_or("Expected argument 2")?)?;
                        chunk.write_code(OpCode::Add, ast.pos_marker.line as u32);
                        self.next_global_pos -= 4;
                    }
                    ASTType::OpVariable("-", OperatorType::Infix) => {
                        self.compile(chunk, vec.get(1).ok_or("Expected argument 1")?)?;
                        self.compile(chunk, vec.get(2).ok_or("Expected argument 2")?)?;
                        chunk.write_code(OpCode::Sub, ast.pos_marker.line as u32);
                        self.next_global_pos -= 4;
                    }
                    ASTType::OpVariable("-", OperatorType::Prefix) => {
                        self.compile(chunk, vec.get(1).ok_or("Expected argument 1")?)?;
                        chunk.write_code(OpCode::Negate, ast.pos_marker.line as u32);
                    }
                    ASTType::OpVariable("*", OperatorType::Infix) => {
                        self.compile(chunk, vec.get(1).ok_or("Expected argument 1")?)?;
                        self.compile(chunk, vec.get(2).ok_or("Expected argument 2")?)?;
                        chunk.write_code(OpCode::Mul, ast.pos_marker.line as u32);
                        self.next_global_pos -= 4;
                    }
                    ASTType::OpVariable("/", OperatorType::Infix) => {
                        self.compile(chunk, vec.get(1).ok_or("Expected argument 1")?)?;
                        self.compile(chunk, vec.get(2).ok_or("Expected argument 2")?)?;
                        chunk.write_code(OpCode::Div, ast.pos_marker.line as u32);
                        self.next_global_pos -= 4;
                    }
                    ASTType::OpVariable("<", OperatorType::Infix) => {
                        self.compile(chunk, vec.get(1).ok_or("Expected argument 1")?)?;
                        self.compile(chunk, vec.get(2).ok_or("Expected argument 2")?)?;
                        chunk.write_code(OpCode::Lt, ast.pos_marker.line as u32);
                        self.next_global_pos -= 4;
                    }
                    ASTType::Variable("printStr") => {
                        self.compile(chunk, vec.get(1).ok_or("Expected argument 1")?)?;
                        chunk.write_code(OpCode::PrintStr, ast.pos_marker.line as u32);
                        self.next_global_pos -= 8;
                    }
                    _ => todo!("Unknown function")
                }
            },
            _ => todo!("Dunno how to compile this")
        }
        Ok(())
    }

}

