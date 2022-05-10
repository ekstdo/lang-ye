#![feature(char_indices_offset)]
#![feature(box_patterns)]


mod parsing;

use parsing::parser;

mod static_analysis;
mod code_gen;
mod vm;

use vm::vm::{VM, RuntimeError};
use vm::chunk::{Chunk, OpCode};

use code_gen::compiler::Compiler;


fn main() -> std::io::Result<()> {
    let mut chunk = Chunk::new();

    let mut vm = VM::new();


    let text = std::fs::read_to_string("./test.ye")?;
    let lines = text.split('\n').collect::<Vec<_>>();
    let mut desugarer = parser::Desugarer::new();
    let mut asts = Vec::new();
    let mut cmperr = false;

    let mut parser = parser::Parser::from_string(&text);
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
