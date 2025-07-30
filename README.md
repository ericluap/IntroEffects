# IntroEffects

A implementation of the language in "An Introduction to Algebraic Effects and Handlers" by Pretnar. You can write in the language using syntax to similar to that from the paper and then evaluate it or infer its type. 

`Main.lean` contains all the examples from the paper.

The small step semantics are formalized in `IntroEffects/SmallStep.lean` where their determinism is proved. Then the evaluater is defined in `IntroEffects/Eval.lean` and proved to match the small step semantics. The proof of Theorem 4.2 (Safety) from the paper is missing at the moment.
