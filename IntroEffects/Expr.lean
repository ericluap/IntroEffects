/-!
  Define the basic parts of the language:
  `Computation`, `Value`, and `Handler`
-/

abbrev Name := String

/--
  Locally nameless, i.e.
  free variables have names and bound variables have de Bruijn indices
-/
inductive Var where
| fvar : Name → Var
| bvar : Nat → Var
deriving Repr, DecidableEq
open Var

/-
  Define `Value`, `Computation`, and `Handler`.
-/
mutual

/--
  Values are inert, i.e.
  they are fixed by small steps.

  A value can be a variable, boolean, lambda function,
  or a handler.
-/
inductive Value where
| var : Var → Value
| bool : Bool → Value
| string : String → Value
| num : Int → Value
| unit : Value
| pair : Value → Value → Value
/-- Assumes that the computation passed in has a dangling bvar -/
| lam : Computation → Value
/-- Assumes that the computation passed in has two dangling bvars.
  The outermost dangling bvar will refer to the function itself,
  the inner one is the normal argument.
 -/
| recfun : Computation → Value
| hdl : Handler → Value
deriving BEq

inductive Computation where
| ret : Value → Computation
/--
  An operation call consists of the name of the operation,
  a value acting as a parameter, and
  a continuation that uses the result of the operation call.

  Assumes that the computation passed in has one dangling bvar.
-/
| opCall : Name → Value → Computation → Computation
/--
  A bind call consists of a computation
  and a continuation that uses the result of the first computation.

  Assumes that the second computation has one dangling bvar.
-/
| bind : Computation → Computation → Computation
| ite (val : Value) (trueBranch falseBranch : Computation)
| app : Value → Value → Computation
/--
  Handle the given computation using the handler.
  (What if the value given is not `.hdl`?)
-/
| handle : Value → Computation → Computation
| join : Value → Value → Computation
| fst : Value → Computation
| snd : Value → Computation
| add : Value → Value → Computation
| sub : Value → Value → Computation
| mul : Value → Value → Computation
| max : Value → Value → Computation
| lt : Value → Value → Computation
| eq : Value → Value → Computation
deriving BEq


structure OpClause where
  op : Name
  /-- Assumes that the body has two dangling bvars. -/
  body : Computation
deriving Repr, BEq

structure Handler where
  /-- Assumes that the computation has one dangling bvar. -/
  ret? : Option Computation
  ops  : List OpClause
deriving Repr, BEq

end
