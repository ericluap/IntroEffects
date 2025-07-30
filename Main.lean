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

-- You can view the term without any syntax sugar
/--
info: do x0 ← print⟨"What is your forename?"; fun x0 ↦ return x0⟩ in
 do x1 ← read⟨(); fun x1 ↦ return x1⟩ in
 do x2 ← print⟨"What is your surname?"; fun x2 ↦ return x2⟩ in
 do x3 ← read⟨(); fun x3 ↦ return x3⟩ in
 join(x1, x3)
-/
#guard_msgs in
#eval printFullName

def alwaysRead := {{{
  fun s ↦ (return handler {ops := ["read"(x,k) ↦ k s, "print"(x,k) ↦ k ()]})
}}}

/--
info: return "Bob Bob"
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
info: return ((), "A B C")
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
info: return ((), "C B A")
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
info: return ((), "A B C")
-/
#guard_msgs in
#evalLang {{{
  do f ← (with ~collect' handle ~abc) in
  f (str "")
}}}

def choose := {{{
  fun xy ↦
    do b ← decide⟨()⟩ in
    if b then fst xy else snd xy
}}}

def pickTrue := {{{
  handler {ops := ["decide"(_x, k) ↦ k True]}
}}}

def chooseDiff := {{{
  do x₁ ← ~choose pair(15,30) in
  do x₂ ← ~choose pair(5,10) in
  x₁ - x₂
}}}

/--
info: return 10
-/
#guard_msgs in
#evalLang {{{
  with ~pickTrue handle ~chooseDiff
}}}

def pickMax := {{{
  handler {ops := ["decide"(_x, k) ↦
    do xt ← k True in
    do xf ← k False in
    max(xt, xf)
  ]}
}}}

/--
info: return 25
-/
#guard_msgs in
#evalLang {{{
  with ~pickMax handle ~chooseDiff
}}}

def chooseInt := {{{
  recfun chooseInt mn ↦
    do m ← fst mn in
    do n ← snd mn in
    do isNLtM ← n < m in
    if isNLtM then
      fail⟨()⟩
    else
      do b ← decide⟨()⟩ in
      if b then (return m) else
      do mPlusOne ← m + 1 in
      chooseInt pair(mPlusOne, n)
}}}

/--
  Returns a pair of type `Bool × Int`
  which is whether or not it is a square number,
  and, if it is, what its square root is.
-/
def isSquare := {{{
  fun n ↦
  (recfun isSquareAux nAcc ↦
    do n ← fst nAcc in
    do acc ← snd nAcc in
    do accSquared ← acc * acc in
    do isNLtAccSquared ← n < accSquared in
    if isNLtAccSquared then
      return pair(False, 0)
    else
      do isNEqAccSquared ← n == accSquared in
      if isNEqAccSquared then
        return pair(True, acc)
      else
        do accPlusOne ← acc + 1 in
        isSquareAux pair(n, accPlusOne)) pair(n, 0)
}}}

def pythagorean := {{{
  fun mn ↦
    do m ← fst mn in
    do n ← snd mn in
    do nMinusOne ← n - 1 in
    do a ← ~chooseInt pair(m, nMinusOne) in
    do aPlusOne ← a + 1 in
    do b ← ~chooseInt pair(aPlusOne, n) in
    do aSquared ← a * a in
    do bSquared ← b * b in
    do a2Plusb2 ← aSquared + bSquared in
    do (isSquare, sqrt) ← ~isSquare a2Plusb2 in
    if isSquare then
      return pair(a, pair(b, sqrt))
    else
      fail⟨()⟩
}}}

def backtrack := {{{
  handler {ops := ["decide"(_x, k) ↦
    with
      handler {ops := ["fail"(_x,_k) ↦ k False]}
    handle
      k True
  ]}
}}}

/--
info: return (5, (12, 13))
-/
#guard_msgs in
#evalLang {{{
  with ~backtrack handle ~pythagorean pair(4,15)
}}}

-- Returns the unhandled `fail` operation
#evalLang {{{
  with ~backtrack handle ~pythagorean pair(10,15)
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
info: return "Hello, world!"
-/
#guard_msgs in
#eval main
