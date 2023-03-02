use super::chunk::{Chunk, OpCode};

use std::io::Write;

pub struct VM {
    ip: usize,
    stack: Vec<u8>,
    stdout: std::io::Stdout
}

pub enum RuntimeError {
    StdoutWriteErr(std::io::Error)
}

impl VM {
    pub fn new() -> VM {
        VM { ip: 0, stack: Vec::new(), stdout: std::io::stdout() }
    }

    pub fn pop_int(&mut self) -> i32 {
        let (a, b, c, d) = (self.stack.pop(), self.stack.pop(), self.stack.pop(), self.stack.pop());
        i32::from_be_bytes([a.unwrap(), b.unwrap(), c.unwrap(), d.unwrap()])
    }

    pub fn pop_bool(&mut self) -> bool {
        self.stack.pop().unwrap() != 0
    }

    pub fn push_int(&mut self, i: i32) {
        self.stack.extend_from_slice(&i32::to_le_bytes(i));
    }

    pub fn push_bool(&mut self, b: bool) {
        self.stack.push(b as u8);
    }

    pub fn interpret(&mut self, chunk: Chunk) -> Result<(), RuntimeError> {
        self.ip = 0;
        loop {
            let instruction = chunk.code[self.ip];

            println!("Current instruction: {}", instruction);
            println!("Current stack: {:?}", self.stack);

            if instruction == OpCode::Return as u8 {
                let return_value = self.pop_int();
                print!("{}\n", return_value);
                return Ok(());
            } else if instruction == OpCode::Int as u8 {
                let index = chunk.get_index(self.ip);
                self.stack.extend_from_slice(&chunk.values[index..index + 4]);
                self.ip += 4;
            } else if instruction == OpCode::Ref as u8 {
                let index = chunk.get_index(self.ip);
                self.stack.extend_from_slice(&u32::to_le_bytes(index as u32));
                self.ip += 4;
            }  else if instruction == OpCode::GetGlobal as u8 {
                let index = chunk.get_index(self.ip);
                let value = (&self.stack[index..index + 4]).to_owned();
                self.stack.extend_from_slice(&value);
                self.ip += 4;
            } else if instruction == OpCode::Negate as u8 {
                let val = self.pop_int();
                self.push_int(-val);
            } else if instruction == OpCode::Add as u8 {
                let val1 = self.pop_int();
                let val2 = self.pop_int();
                self.push_int(val2 + val1);
            } else if instruction == OpCode::Sub as u8 {
                let val1 = self.pop_int();
                let val2 = self.pop_int();
                self.push_int(val2 - val1);
            } else if instruction == OpCode::Mul as u8 {
                let val1 = self.pop_int();
                let val2 = self.pop_int();
                self.push_int(val2 * val1);
            } else if instruction == OpCode::Div as u8 {
                let val1 = self.pop_int();
                let val2 = self.pop_int();
                self.push_int(val2 / val1);
            } else if instruction == OpCode::Lt as u8 {
                let val1 = self.pop_int();
                let val2 = self.pop_int();
                self.push_bool(val2 < val1);
            } else if instruction == OpCode::PrintStr as u8 {
                let strslice = self.pop_int() as usize;
                let strlen = self.pop_int() as usize;
                let string = &chunk.values[strslice..strslice + strlen];
                self.stdout.write(string).map_err(RuntimeError::StdoutWriteErr)?;
            } else {
                println!("Unknown opcode!");
            } 

            self.ip += 1;
        }
    }
}


