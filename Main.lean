import IntroEffects

/-!
  Examples of the language and its output after being evaluated.
-/
open Input

def printFullName := {{{
  do _a ← print(str("What is your forename?"); fun y ↦ (return y)) in
  do forename ← read((); fun y ↦ (return y)) in
  do _b ← print(str("What is your surname?"); fun y ↦ (return y)) in
  do surname ← read((); fun y ↦ (return y)) in
  do joined ← join(forename, surname) in
  return joined
}}}

def alwaysRead := {{{
  fun s ↦ (return handler {ops := ["read"(x,k) ↦ k s, "print"(x,k) ↦ k ()]})
}}}

/--
info: Bob Bob
-/
#guard_msgs in
#evalLang {{{
  do h ← ~alwaysRead str("Bob")  in
  with h handle ~printFullName
}}}

def main : IO Unit :=
  IO.println s!"Hello, !"
