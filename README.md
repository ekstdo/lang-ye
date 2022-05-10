# Ye

A new educational programming language, that was pretty much made for
fun and learning purposes.

## Plans

- functional programming language, but not purely functional
- static typing




## Roadmap

- [ ] Parser
	- [X] Lexer
	- [ ] Preprocessor
	- [X] Parser
- [ ] Static Analysis
	- [ ] Type checking
	- [ ] Optimizations
- [ ] Compiler
	- [ ] Code gen
- [ ] Virtual Machine
	- [X] simple instructions
	- [ ] we need moooore ...

## Syntax


```
let a = 5; ## Type inference

let b: I32 = 7;

let f x = x + 5;

let g x : I32 -> I32 = x + 10;

## Control structures

if f 4 < 3 {
	print "yo, f 4 is less than 3";
} else if g 4 < 3 {
	print "something, something, something";
} else {
	print "idk";
}; ## `if/else` might return an expression, so you need ;

for i in 0..10 {
	print "\(i)";
}

for (let i = 0; i < 10; i += 1) {
	print "old style \(i)";
}

for i in 0..=20 {
	if i == 10 {
		break;
	}
	print "yay, a number :D";
} else { ## for else statements
	print "idk, how you didn't break this???";
}

let mut b = 0; ## immutability is default

while b < 100 {
	if b == 5 {
		print "OUh! 5 is my favorite number ^^";
		continue;
	}
	print "\(b) is still less than 100";
}
```
