# Hoare Logic

Floyd-Hoare logic builds upon the idea that before executing something a line of code or an operation in assembly, there are preconditions and there are postconditions.

Think about executing a move instruction where some location of memory is read into a register. Before the move instruction, the register has some value in it. It may be initally 0, or something else. After, however, the value in the register is what was stored at that location in memory.

Hoare logic allows for us to build statements about programs line by line, and prove them correct.

There are two kinds of correctness in Hoare logic, partial correctness and total correctness. Partial correctness means that if the precondition holds, the command will either never terminate or will terminate and the postcondition will hold. Total correctness means that if the precondition holds, the command will always finish and will hold.

If we have partial correctness {True} while(true); {True} is a correct statement. If we have total correctness however, this is not correct.

I am going to stick to proving things with partial correctness.

## Hoare Logic Rules for Partial Correctness

NO-OP rule: {P} NO-OP {P}

Assignment rule: {P subtitute a for x} x := a {P}

Where in the pre-condition we substitue a for any occurence of x.

Composition rule: {P} c1 {Q} and {Q} c2 {R} implies {P} c1;c2 {R}

Conditional rule: {B & P} c1 {Q} and {~B & P} c2 {Q} implies {P} if B then c1 else c2 {Q}

Consequence rule: P implies P' and Q' implies Q and {P'}c{Q'} imply {P}c{Q}.

While rule: {P & B}c{P} implies {P} while B do c {P & ~B}.

Note you can find all of these on [Wikipedia](https://en.wikipedia.org/wiki/Hoare_logic).
