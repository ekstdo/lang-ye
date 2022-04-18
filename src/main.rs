#![feature(char_indices_offset)]
#![feature(box_patterns)]

use parser::{AST, ASTType, OperatorType};

mod parser;
mod typing;

use std::{str, io::Write};

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
enum OpCode {
    Return,
    Negate,
    Add, Sub, Mul, Div,
    Int, Bool, Ref, PrintStr,
    Lt,

    DefineGlobal, GetGlobal
}

struct Chunk {
    code: Vec<u8>,
    values: Vec<u8>,
    lines: Vec<(u32, u32)>
}

impl Chunk {
    fn new() -> Chunk {
        Chunk { code : Vec::new(), values : Vec::new(), lines: Vec::new() }
    }

    fn write_code(&mut self, code: OpCode, line: u32){
        self.code.push(code as u8);
        match self.lines.last_mut() {
            Some ((last, _amt)) if *last != line => self.lines.push((line, 1)),
            Some ((_last, amt)) => *amt += 1,
            None => self.lines.push((line, 1))
        }
    }

    fn get_index(&self, offset: usize) -> usize {
        u32::from_le_bytes(self.code[offset + 1.. offset + 5].try_into().unwrap()) as usize
    }

    fn disassemble(&self, mut offset: usize){
        println!("== disassemble chunk ==");
        let mut line_counter = 0;
        let mut line_index = 0;
        while offset < self.code.len() {
            let i = self.code[offset];
            print!("{:04} ", offset);

            if line_counter == 0 {
                print!(" {:5} ", self.lines[line_index].0);
                line_counter = self.lines[line_index].1;
                line_index += 1;
            } else {
                line_counter -= 1;
                print!("     | ");
            }

            let simple_instructions = vec![OpCode::Return, OpCode::PrintStr, OpCode::Lt, OpCode::Negate, OpCode::Add, OpCode::Sub, OpCode::Mul, OpCode::Div];
            let mut is_simple = false;

            for j in simple_instructions {
                if i  == j as u8 {
                    println!("{:?}", j);
                    offset += 1;
                    is_simple = true;
                    break;
                }
            }

            if is_simple {
                continue;
            }

            if i == OpCode::Int as u8 {
                let index = self.get_index(offset);
                let num = i32::from_le_bytes(self.values[index..index + 4].try_into().unwrap());
                println!("{:?} : {} at {}", OpCode::Int, num, index);
                offset += 5;
            } else if i == OpCode::Ref as u8 {
                let index = self.get_index(offset);
                println!("{:?} : at {}", OpCode::Ref, index);
                offset += 5;
            }  else if i == OpCode::GetGlobal as u8 {
                let index = self.get_index(offset);
                println!("{:?} : at {}", OpCode::GetGlobal, index);
                offset += 5;
            }else {
                println!("Unknown opcode!");
                offset += 1;
            }
        }

        println!("\n\n== value array of chunk ==");
        offset = 0;
        while offset < self.values.len() {
            if offset % 4 == 0 {
                print!("\n{:<5}: ", offset);
            }
            print!("{} ", self.values[offset]);
            offset += 1;
        }
        print!("\n");
    }

    fn add_int(&mut self, val: i32) -> usize {
        let offset = self.values.len();
        self.values.extend(i32::to_le_bytes(val));
        offset
    }

    fn add_slice(&mut self, val: &[u8]) -> usize {
        let offset = self.values.len();
        self.values.extend(val);
        offset
    }

    fn write_value(&mut self, pos: u32, bytes: u32, line: u32){
        let slice : [u8;4] = u32::to_le_bytes(pos as u32).into();
        self.code.extend(slice);
        match self.lines.last_mut() {
            Some ((last, _)) if *last != line => self.lines.push((line, bytes)),
            Some ((_, amt)) => *amt += bytes,
            None => self.lines.push((line, bytes))
        }
    }
}

struct VM {
    ip: usize,
    stack: Vec<u8>,
    stdout: std::io::Stdout
}
enum RuntimeError {
    StdoutWriteErr(std::io::Error)
}

impl VM {
    fn new() -> VM {
        VM { ip: 0, stack: Vec::new(), stdout: std::io::stdout() }
    }

    fn pop_int(&mut self) -> i32 {
        let (a, b, c, d) = (self.stack.pop(), self.stack.pop(), self.stack.pop(), self.stack.pop());
        i32::from_be_bytes([a.unwrap(), b.unwrap(), c.unwrap(), d.unwrap()])
    }

    fn pop_bool(&mut self) -> bool {
        self.stack.pop().unwrap() != 0
    }

    fn push_int(&mut self, i: i32) {
        self.stack.extend_from_slice(&i32::to_le_bytes(i));
    }

    fn push_bool(&mut self, b: bool) {
        self.stack.push(b as u8);
    }

    fn interpret(&mut self, chunk: Chunk) -> Result<(), RuntimeError> {
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

struct Compiler {
    globals: std::collections::HashMap<String, u32>,
    next_global_pos: u32
}

impl Compiler {
    fn new() -> Self {
        Self { globals: std::collections::HashMap::new(), next_global_pos: 0 }
    }

    fn compile<'a>(&mut self, chunk: &mut Chunk, ast: &AST<'a>) -> Result<(), &'static str> {
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
                for (var, val, static_, mut_) in v {
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



fn main() -> std::io::Result<()> {
    let mut chunk = Chunk::new();

    let mut vm = VM::new();


    let text = std::fs::read_to_string("./test.ye")?;
    let lines = text.split('\n').collect::<Vec<_>>();
    let scanner = parser::Scanner::new(&text);
    let mut desugarer = parser::Desugarer::new();
    let mut asts = Vec::new();
    let mut cmperr = false;

    let mut parser = parser::Parser::new(scanner);
    loop {
        let parsed = match parser.next() {
            Some(x) => x,
            None => break
        };
        match parsed {
            Ok(ast) =>{
                println!("{}", ast);
                let desugared = desugarer.desugar(ast);
                println!("desugared: {}", desugared);
                asts.push(desugared)
            },
            Err(s) => { parser.handle_error(&lines, s); cmperr = true; }
        }
    }

    if cmperr {
        return Ok(());
    }

    let mut compiler = Compiler::new();

    for i in asts {
        match compiler.compile(&mut chunk, &i) {
            Ok(_) => (),
            Err(e) => println!("Compile error: {}", e)
        }
    }

    chunk.write_code(OpCode::Return, 12);

    chunk.disassemble(0);

    match vm.interpret(chunk) {
        Ok(_) => (),
        Err(RuntimeError::StdoutWriteErr(err)) => println!("RUNTIME ERROR:\nA standart output write error occured!: {}", err)
    }

    Ok(())
}
