# Super tiny HOL proof assistant in lean

This material is a proof-of-concept code of my hypothesis that writing a prover will be much easier if I take a proof assistant as its implementation language.
An explanatory article about this project will be available soon at techbookfest 2019 spring.

I didn't implement a large part of language features which a proof assistant needs for being called a proof assistant. Instead they are realized by free riding on the metalanguage; I didn't implement:

- parser (it's a DSL)
- binding structure (use HOAS)
- type checker (Lean's type checker checks it)
- type inference (Lean's unifier infers it)
- (efficient) evaluator (use the NbE technique)
- tactic language (Lean's tactic language serves it)

That's why the code is very small (< 300 LoC).

I separate from the main file (`hol.lean`) some codes I additionally wrote to write my article. Mainly looking at `hol.lean` should suffice if you know its technical backgrounds already.