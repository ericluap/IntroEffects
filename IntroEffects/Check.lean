import IntroEffects.Syntax
import IntroEffects.Inference

def checkValType (op : OpSignatureList) (v : Value) (t : ValueTy) : Bool := (do
  let type ← inferValType op v
  let constraint : Constraints := [.valEq type t]
  unify constraint).toBool

def checkCompType (op : OpSignatureList) (c : Computation) (t : ComputationTy) : Bool := (do
  let type ← inferCompType op c
  let constraint : Constraints := [.valEq type.returnTy t.returnTy]
  unify constraint).toBool

def checkType (op : OpSignatureList) (e : Expr) (t : Ty) : Bool :=
  match e, t with
  | .val v, .val vt => checkValType op v vt
  | .comp c, .comp ct => checkCompType op c ct
  | _, _ => false

open Input
#eval checkType [] {{{
  fun x ↦ x + 1
}}}  (.val (.function .num ⟨.num, []⟩))
