import IntroEffects

/-!
  Examples of the language and its output after being evaluated.
-/
open Input

def printFullName := {{{
  ← print⟨str "What is your forename?"⟩;
  do forename ← read⟨()⟩ in
  ← print⟨str "What is your surname?"⟩;
  do surname ← read⟨()⟩ in
  join(forename, surname)
}}}

def alwaysRead := {{{
  fun s ↦ (return handler {ops := ["read"(x,k) ↦ k s, "print"(x,k) ↦ k ()]})
}}}

/--
info: "Bob Bob"
-/
#guard_msgs in
#evalLang {{{
  do h ← ~alwaysRead (str "Bob") in
  with h handle ~printFullName
}}}


-- We can also view all the reductions done
/--
info: fun x0 ↦  if x0  then return "hi"  else return "bye" False

if False  then return "hi"  else return "bye"

return "bye"
-/
#guard_msgs in
#evalLangTrace {{{
    ((fun x ↦ if x then return (str "hi") else return (str "bye")) False)
}}}

def abc := {{{
  ← print⟨str "A"⟩;
  ← print⟨str "B"⟩;
  print⟨str "C"⟩
}}}

def collect := {{{
  handler {
    return x ↦ return pair(x, str ""),
    ops := [
      "print"(s, k) ↦
        do (x, acc) ← k () in
        do joined ← join(s, acc) in
        return pair(x, joined)
    ]
  }
}}}

/--
info: ((), "A B C")
-/
#guard_msgs in
#evalLang {{{
  with ~collect handle ~abc
}}}

def reverse := {{{
  handler {
    ops := ["print"(s,k) ↦ ← k (); print⟨s⟩]
  }
}}}

/--
info: ((), "C B A")
-/
#guard_msgs in
#evalLang {{{
  with ~collect handle
  with ~reverse handle ~abc
}}}

def collect' := {{{
  handler {
    return x ↦ return (fun acc ↦ (return pair(x, acc))),
    ops := [
      "print"(s, k) ↦
        return (fun acc ↦
          (do res ← k () in
          do joined ← join(acc, s) in
          res joined))
    ]
  }
}}}

/--
info: ((), "A B C")
-/
#guard_msgs in
#evalLang {{{
  do f ← (with ~collect' handle ~abc) in
  f (str "")
}}}

def main : IO Unit :=
  let hello_world := evalLang {{{
    do (_a, out) ←
      with ~collect handle
        ← print⟨str "Hello,"⟩;
        print⟨str "world!"⟩
      in
    return out
  }}}

  IO.println hello_world

/--
info: "Hello, world!"
-/
#guard_msgs in
#eval main
