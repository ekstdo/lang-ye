#![feature(char_indices_offset)]
#![feature(box_patterns)]

mod parser;

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
enum OpCode {
    Return,
    Negate,
    Add, Sub, Mul, Div,
    Int
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

            let simple_instructions = vec![OpCode::Return, OpCode::Negate, OpCode::Add, OpCode::Sub, OpCode::Mul, OpCode::Div];
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
            } else {
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
    chunk: Option<Chunk>,
    ip: usize,
    stack: Vec<u8>
}

enum InterpretResult {
    Ok, CompileError, RuntimeError
}

impl VM {
    fn new() -> VM {
        VM { chunk: None, ip: 0, stack: Vec::new() }
    }

    fn pop_int(&mut self) -> i32 {
        let (a, b, c, d) = (self.stack.pop(), self.stack.pop(), self.stack.pop(), self.stack.pop());
        i32::from_be_bytes([a.unwrap(), b.unwrap(), c.unwrap(), d.unwrap()])
    }

    fn push_int(&mut self, i: i32) {
        self.stack.extend_from_slice(&i32::to_le_bytes(i));
    }

    fn interpret(&mut self, chunk: Chunk) -> InterpretResult {
        self.ip = 0;
        loop {
            let instruction = chunk.code[self.ip];

            if instruction == OpCode::Return as u8 {
                let return_value = self.pop_int();
                print!("{}\n", return_value);
                return InterpretResult::Ok;
            } else if instruction == OpCode::Int as u8 {
                let index = chunk.get_index(self.ip);
                self.stack.extend_from_slice(&chunk.values[index..index + 4]);
                self.ip += 4;
            } else if instruction == OpCode::Negate as u8 {
                let val = self.pop_int();
                self.push_int(-val);
            } else if instruction == OpCode::Add as u8 {
                let val1 = self.pop_int();
                let val2 = self.pop_int();
                self.push_int(val1 + val2);
            } else if instruction == OpCode::Sub as u8 {
                let val1 = self.pop_int();
                let val2 = self.pop_int();
                self.push_int(val1 - val2);
            } else if instruction == OpCode::Mul as u8 {
                let val1 = self.pop_int();
                let val2 = self.pop_int();
                self.push_int(val1 * val2);
            } else if instruction == OpCode::Div as u8 {
                let val1 = self.pop_int();
                let val2 = self.pop_int();
                self.push_int(val1 + val2);
            } else {
                println!("Unknown opcode!");
            } 

            self.ip += 1;
        }
    }
}

fn main() -> std::io::Result<()> {
    let mut chunk = Chunk::new();
    chunk.write_code(OpCode::Int, 101);
    let pos = chunk.add_int(12);
    chunk.write_value(pos as u32, 4, 101);
    chunk.write_code(OpCode::Negate, 101);
    chunk.write_code(OpCode::Int, 101);
    let pos = chunk.add_int(15);
    chunk.write_value(pos as u32, 4, 101);
    chunk.write_code(OpCode::Add, 101);

    chunk.write_code(OpCode::Return, 101);
    chunk.disassemble(0);
    let mut vm = VM::new();
    vm.interpret(chunk);


    let text = std::fs::read_to_string("./test.ye")?;
    let lines = text.split('\n').collect::<Vec<_>>();
    let mut scanner = parser::Scanner::new(&text);


    let parser = parser::Parser::new(scanner);
    for parsed in parser {
        match parsed {
            Ok(o) => println!("{}", o),
            Err(s) => parser::Parser::handle_error(&lines, s)
        }
    }
    
    // loop {
    //     let n = scanner.next();
    //     println!("{:?} peek: {:?}", n, scanner.peek());
    //     if n.is_none() {
    //         break;
    //     }
    // }

    Ok(())
}
