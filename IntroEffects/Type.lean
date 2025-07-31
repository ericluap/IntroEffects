import Std
import IntroEffects.Expr
import Lean

mutual

/--
  The possible types for a value.
-/
inductive ValueTy where
| bool | string | num | void | unit
| pair : ValueTy → ValueTy → ValueTy
| function : ValueTy → ComputationTy → ValueTy
| handler : ComputationTy → ComputationTy → ValueTy
deriving DecidableEq, Repr

/--
  The type of a computation is the type of the value it returns
  as well as the operations it can possibly call.
-/
structure ComputationTy where
  returnTy : ValueTy
  Δ : List String
deriving DecidableEq, Repr
end

notation A "!" Δ => ComputationTy.mk A Δ

/--
  The type of either a value or computation.
-/
inductive Ty where
| val : ValueTy → Ty
| comp : ComputationTy → Ty

instance : Coe ValueTy Ty where
  coe := .val
instance : Coe ComputationTy Ty where
  coe := .comp

/--
  An expression that is either a value or computation.
-/
inductive Expr where
| val : Value → Expr
| comp : Computation → Expr

instance : Coe Value Expr where
  coe := .val
instance : Coe Computation Expr where
  coe := .comp

abbrev OpSignature := Std.TreeMap String (ValueTy × ValueTy)
abbrev Ctx := List ValueTy

def OpSignature.inputType (σ : OpSignature) (s : String)
  (h : s ∈ σ := by grind) := σ.get s h |>.1
def OpSignature.outputType (σ : OpSignature) (s : String)
  (h : s ∈ σ := by grind) := σ.get s h |>.2

/--
  Find the `n`th type in the context
-/
def lookup : Ctx → Nat → Option ValueTy
| [], _ => none
| τ::_, 0 => some τ
| _::Γ, n+1 => lookup Γ n

notation "(" x " : " A ")" " ∈ " Γ => lookup Γ x = some A

/--
  `HasType σ Γ e T` means that `Γ ⊢ e : T`
  with `σ` being the fixed types of all possible operation calls.
-/
inductive HasType (σ : OpSignature) : Ctx → Expr → Ty → Prop where
/--
 If `(x : A) ∈ Γ` then `Γ ⊢ x : A`
-/
| var x A : ((x : A) ∈ Γ) → HasType σ Γ (Value.var (.bvar x)) A
/--
  `Γ ⊢ True : bool` and `Γ ⊢ False : bool`
-/
| bool b : HasType σ Γ (Value.bool b) ValueTy.bool
/--
  If `Γ, x : A ⊢ c : C`, then `Γ ⊢ (fun x => c) : A → C`
-/
| lam A (c : Computation) (C : ComputationTy) :
  HasType σ (A :: Γ) c C → HasType σ Γ (Value.lam c) (ValueTy.function A C)
/--
  If `Γ, x : A ⊢ cᵣ : B!Δ'`, `(opᵢ : Aᵢ → Bᵢ) ∈ Σ`,
  `Γ, x : Aᵢ, k : Bᵢ → B!Δ' ⊢ cᵢ : B!Δ'`, and `Δ \ {opᵢ} ⊆ Δ'`,
  then
  `Γ ⊢ handler {return x ↦ cr, ops := [op₁(x, k) ↦ c₁, ⋯, opₙ(x, k) ↦ cₙ]} : A!Δ ⇒ B!Δ'`
-/
| handler (cr : Computation) :
  HasType σ (A :: Γ) cr (B ! Δ') → -- `Γ, x : A ⊢ cᵣ : B!Δ'`
  (h: ∀opClause ∈ ops, opClause.op ∈ σ) → -- `(opᵢ : Aᵢ → Bᵢ) ∈ Σ`
  (∀mem : opClause ∈ ops,
    let Aᵢ := σ.inputType opClause.op
    let Bᵢ := σ.outputType opClause.op
    let k := ValueTy.function Bᵢ (B ! Δ')
    HasType σ (k :: Aᵢ :: Γ) opClause.body (B ! Δ')
  ) → -- `Γ, x : Aᵢ, k : Bᵢ → B!Δ' ⊢ cᵢ : B!Δ'`
  (Δ.removeAll (ops.map (·.op)) ⊆ Δ') → -- `Δ \ {opᵢ} ⊆ Δ'`
  HasType σ Γ (Value.hdl (Handler.mk cr ops))
    (ValueTy.handler (A ! Δ) (B ! Δ'))
| ret (v : Value) Δ (A : ValueTy) : HasType σ Γ v A →
  HasType σ Γ (Computation.ret v) (A ! Δ)
/--
  If `(op : Aop → Bop) ∈ Σ`, `Γ ⊢ v : Aop`, `Γ, y : Bop ⊢ c : A!Δ`, and `op ∈ Δ`
  then `Γ ⊢ op(v; fun y ↦ c) : A!Δ`

-/
| op (v : Value) (c : Computation) :
  (h : name ∈ σ) → -- `(op : Aop → Bop) ∈ Σ`
  HasType σ Γ v (σ.inputType name) → -- `Γ ⊢ v : Aop`
  HasType σ (σ.outputType name :: Γ) c (A ! Δ) → -- `Γ, y : Bop ⊢ c : A!Δ`
  (name ∈ Δ) → -- `op ∈ Δ`
  HasType σ Γ (Computation.opCall name v c) (A ! Δ)
/--
  If `Γ ⊢ c₁ : A!Δ` and `Γ, x : A ⊢ c₂ : B!Δ`
  then `Γ ⊢ do x ← c₁ in c₂ : B!Δ`
-/
| bind (c₁ c₂ : Computation):
  HasType σ Γ c₁ (A ! Δ) → HasType σ (A :: Γ) c₂ (B ! Δ) →
  HasType σ Γ (Computation.bind c₁ c₂) (B ! Δ)
/--
  If `Γ ⊢ v₁ : A → C` and `Γ ⊢ v₂ : A`
  then `Γ ⊢ v₁ v₂ : C`
-/
| app (v₁ v₂ : Value) :
  HasType σ Γ v₁ (ValueTy.function A C) → HasType σ Γ v₂ A →
  HasType σ Γ (Computation.app v₁ v₂) C
/--
  If `Γ ⊢ v : bool`, `Γ ⊢ c₁ : C`, and `Γ ⊢ c₂ : C`
  then `Γ ⊢ if v then c₁ else c₂ : C`
-/
| ite (v : Value) (c₁ c₂ : Computation) :
  HasType σ Γ v ValueTy.bool → HasType σ Γ c₁ C → HasType σ Γ c₂ C →
  HasType σ Γ (Computation.ite v c₁ c₂) C
/--
  If `Γ ⊢ v : C ⇒ D` and `Γ : c : C`
  then `Γ ⊢ with v handle c : D`
-/
| handle (v : Value) (c : Computation) :
  HasType σ Γ v (ValueTy.handler C D) → HasType σ Γ c C →
  HasType σ Γ (Computation.handle v c) D

/-
  Improve the input syntax for types.
-/
namespace InputType
open Lean Elab Term Meta

declare_syntax_cat type'

scoped syntax "{" type' "}" : type'
scoped syntax "(" type' ", " type' ")" : type'
scoped syntax type' " → " type' : type'
scoped syntax type' " ⇒ " type' : type'
scoped syntax "bool" : type'
scoped syntax "int" : type'
scoped syntax "str" : type'
scoped syntax "unit" : type'
scoped syntax "void" : type'
scoped syntax:max "~" term:max : type'
scoped syntax "[type| " type' " ]" : term

scoped macro_rules
| `([type| {$e1} ]) => `(ComputationTy.mk [type| $e1 ] [])
| `([type| ($e1, $e2) ]) => `(ValueTy.pair [type| $e1 ] [type| $e2 ])
| `([type| $e1 → $e2 ]) => `(ValueTy.function [type| $e1 ] [type| $e2 ])
| `([type| $e1 ⇒ $e2 ]) => `(ValueTy.handler [type| $e1 ] [type| $e2 ])
| `([type| bool ]) => `(ValueTy.bool)
| `([type| int ]) => `(ValueTy.num)
| `([type| str ]) => `(ValueTy.string)
| `([type| unit ]) => `(ValueTy.unit)
| `([type| void ]) => `(ValueTy.void)
| `([type| ~$e1 ]) => pure e1
end InputType

namespace InputSigma
declare_syntax_cat sigma

scoped syntax "(" str ", " type' " ⟶ " type' ")" : sigma
scoped syntax "[σ| " sigma,* "]" : term

macro "[σ| " elems:sigma,* "]" : term => do
  let elems := elems.getElems
  let transformed ← elems.mapM fun stx =>
    match stx with
    | `(sigma| ( $s, $e1 ⟶ $e2 )) =>
      open InputType in `(($s, ([type| $e1], [type| $e2])))
    | _ => Lean.Macro.throwError s!"Unsupported syntax {stx}"
  `([$transformed,*])


end InputSigma
