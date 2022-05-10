#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum OpCode {
    Return,
    Negate,
    Add, Sub, Mul, Div,
    Int, Bool, Ref, PrintStr,
    Lt,

    DefineGlobal, GetGlobal
}

pub struct Chunk {
    pub code: Vec<u8>,
    pub values: Vec<u8>,
    pub lines: Vec<(u32, u32)>
}

impl Chunk {
    pub fn new() -> Chunk {
        Chunk { code : Vec::new(), values : Vec::new(), lines: Vec::new() }
    }

    pub fn write_code(&mut self, code: OpCode, line: u32){
        self.code.push(code as u8);
        match self.lines.last_mut() {
            Some ((last, _amt)) if *last != line => self.lines.push((line, 1)),
            Some ((_last, amt)) => *amt += 1,
            None => self.lines.push((line, 1))
        }
    }

    pub fn get_index(&self, offset: usize) -> usize {
        u32::from_le_bytes(self.code[offset + 1.. offset + 5].try_into().unwrap()) as usize
    }

    pub fn disassemble(&self, mut offset: usize){
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

    pub fn add_int(&mut self, val: i32) -> usize {
        let offset = self.values.len();
        self.values.extend(i32::to_le_bytes(val));
        offset
    }

    pub fn add_slice(&mut self, val: &[u8]) -> usize {
        let offset = self.values.len();
        self.values.extend(val);
        offset
    }

    pub fn write_value(&mut self, pos: u32, bytes: u32, line: u32){
        let slice : [u8;4] = u32::to_le_bytes(pos as u32).into();
        self.code.extend(slice);
        match self.lines.last_mut() {
            Some ((last, _)) if *last != line => self.lines.push((line, bytes)),
            Some ((_, amt)) => *amt += bytes,
            None => self.lines.push((line, bytes))
        }
    }
}

