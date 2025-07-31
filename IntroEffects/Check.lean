import IntroEffects.Syntax
import IntroEffects.Inference

/--
  Check whether the value `v` has value type `t`.
-/
def checkValType (op : OpSignatureList) (t : ValueTy) (v : Value) : Bool := (do
  let type ← inferValType op v
  let constraint : Constraints := [.valEq type t]
  unify constraint).toBool

/--
  Check whether the computation `c` has computation type `t`.
-/
def checkCompType (op : OpSignatureList) (t : ComputationTy) (c : Computation) : Bool := (do
  let type ← inferCompType op c
  let constraint : Constraints := [.valEq type.returnTy t.returnTy]
  unify constraint).toBool

/--
  Check whether the given expression has the given type.
-/
def checkType (op : OpSignatureList) : Ty → Expr →  Bool
| .val vt, .val v => checkValType op vt v
| .comp ct, .comp c => checkCompType op ct c
| _, _ => false

open Input InputType
#eval checkType [] [type| int → {int} ] {{{
  fun x ↦ x + 1
}}}
