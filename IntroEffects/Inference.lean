import IntroEffects.Type
import IntroEffects.Syntax
import Batteries.Data.List

mutual

/--
  The possible types for a value.
  This is the same as `ValueTy` but with metavariables.
-/
inductive ValueTy' where
| bool
| function : ValueTy' → ComputationTy' → ValueTy'
| handler : ComputationTy' → ComputationTy' → ValueTy'
| mvar : Nat → ValueTy'
deriving Repr, DecidableEq

/--
  The type of a computation is the type of the value it returns.
-/
structure ComputationTy' where
  returnTy : ValueTy'
deriving Repr, DecidableEq
end

/--
  A constraint says that two types must be equal.
  This constrains what actual types a metavariable couuld have.
-/
inductive Constraint where
| valEq (τ τ' : ValueTy') -- `τ ≡ τ'`
deriving Repr

/--
  A bound variable has the type of the type it refers to in the context.
-/
abbrev Ctx' := List ValueTy'
/--
  An operation signature matches the name of the operation
  to its input type and output type.
-/
abbrev OpSignature' := Std.TreeMap String (ValueTy × ValueTy)
abbrev Constraints := List Constraint

mutual
def valueTyToPrime : ValueTy → ValueTy'
| .bool => .bool
| .handler c1 c2 => .handler (compTyToPrime c1) (compTyToPrime c2)
| .function v c => .function (valueTyToPrime v) (compTyToPrime c)

def compTyToPrime : ComputationTy → ComputationTy'
| ⟨returnTy, _⟩ => ⟨valueTyToPrime returnTy⟩
end

instance : Coe ValueTy ValueTy' where
  coe := valueTyToPrime

/--
  Track the current number of mvars so that we can create unique ones easily.
-/
structure MVarState where
  next : Nat := 0
deriving Repr

/--
  Handle errors and create fresh mvars.
-/
abbrev MetaM := ExceptT String (StateM MVarState)

/--
  Create a fresh value type mvar.
-/
def freshValueMVar : MetaM ValueTy' := do
  let n ← get <&> (·.next)
  modify (fun s => {next := s.next + 1})
  return (.mvar n)

/--
  Create a fresh computation type mvar.
-/
def freshCompMVar : MetaM ComputationTy' := do
  return ({returnTy := ←freshValueMVar})

/-
  Return the type with metavariables along with
  constraints on those metavariables.
-/
mutual
def collectValConstraints (σ : OpSignature') (Γ : Ctx') :
    Value → MetaM (ValueTy' × Constraints)
| .var (.bvar i) =>
  match Γ[i]? with
  | some τ => pure (τ, [])
  | none => Except.error s!"Unbound de Bruijn index {i}"
| .bool _ => pure (.bool, [])
| .hdl h => collectHandlerConstraints σ Γ h
| .lam body => do
  -- Since `body` has one dangling bvar, add a mvar to the context.
  let α ← freshValueMVar
  let (k, C) ← collectCompConstraints σ (α :: Γ) body
  return (.function α k, C)
| v => Except.error s!"Unsupported value {v}"
/-
| .recfun body => do
  let α ← freshValueMVar
  let β ← freshValueMVar
  let (k, C) ← collectCompConstraints (α :: β :: Γ) body
  return (.function α k, C)
| .pair a b => do
  let (τa, Ca) ← collectValConstraints σ Γ a
  let (τb, Cb) ← collectValConstraints σ Γ b
  return (.pair τa τb, Ca ++ Cb)-/

def collectCompConstraints (σ : OpSignature') (Γ : Ctx') :
    Computation → MetaM (ComputationTy' × Constraints)
| .ret v => do
  let (τ, C) ← collectValConstraints σ Γ v
  return (.mk τ, C)
| .opCall name v cont => do
  let some (Aop, Bop) := (σ.get? name) | Except.error s!"Unknown op {name}"
  let (τ_v, C_v) ← collectValConstraints σ Γ v

  -- `cont` has one dangling bvar
  let y ← freshValueMVar
  let (τ_cont, C_cont) ← collectCompConstraints σ (y :: Γ) cont

  let newConstraints : Constraints := [
    .valEq τ_v Aop, -- `Γ ⊢ v : Aop`
    .valEq y Bop, -- `Γ ⊢ y : Bop`
  ]
  return ({returnTy := τ_cont.returnTy}, newConstraints ++ C_v ++ C_cont)
| .bind c1 c2 => do
  let (_τ_c1, C_c1) ← collectCompConstraints σ Γ c1

  -- `c2` has one dangling bvar
  let α ← freshValueMVar
  let (τ_c2, C_c2) ← collectCompConstraints σ (α :: Γ) c2

  return ({returnTy := τ_c2.returnTy}, C_c1 ++ C_c2)
| .app v1 v2 => do
  let (τ1, C1) ← collectValConstraints σ Γ v1
  let (τ2, C2) ← collectValConstraints σ Γ v2
  let α ← freshCompMVar
  let newConstraint : Constraints := [.valEq τ1 (.function τ2 α)]
  return (α, newConstraint ++ C1 ++ C2)
| .ite b c1 c2 => do
  let (τb, Cb) ← collectValConstraints σ Γ b
  let (τ1, C1) ← collectCompConstraints σ Γ c1
  let (τ2, C2) ← collectCompConstraints σ Γ c2
  let newConstraints : Constraints := [
    .valEq τb .bool,
    .valEq τ1.returnTy τ2.returnTy
  ]
  return ({returnTy := τ1.returnTy},
    newConstraints ++ C1 ++ C2 ++ Cb)
| .handle h c => do
  let (.handler startType endType, Ch) ← collectValConstraints σ Γ h
    | Except.error s!"Expected a handler but was given {h}"
  let (τc, Cc) ← collectCompConstraints σ Γ c
  let newConstraints : Constraints := [.valEq startType.returnTy τc.returnTy]
  return (endType, newConstraints ++ Ch ++ Cc)
| c => Except.error s!"Unsupported computation {c}"

def collectOpClauseConstraints (σ : OpSignature') (Γ : Ctx') :
    OpClause → MetaM (ComputationTy' × Constraints)
| ⟨op, body⟩ => do
  let some (Aop, Bop) := (σ.get? op) | Except.error s!"Unknown op {op}"

  -- `body` has two dangling bvars
  let α ← freshValueMVar
  let (τ_body, C_body) ← collectCompConstraints σ (α :: Aop :: Γ) body

  let newConstraints : Constraints := [.valEq α (.function Bop τ_body)]
  return (τ_body, newConstraints ++ C_body)

def collectHandlerConstraints (σ : OpSignature') (Γ : Ctx') :
    Handler → MetaM (ValueTy' × Constraints)
| ⟨ret, ops⟩ => do
  -- `ret` has one dangling bvar
  let α ← freshValueMVar
  let (τret, Cret) ← collectCompConstraints σ (α :: Γ) ret
  let opsTypes ← ops.mapM (collectOpClauseConstraints σ Γ ·)
  let newConstraints : Constraints := opsTypes.map (.valEq ·.1.returnTy τret.returnTy)
  return (.handler ⟨α⟩ τret, Cret ++ newConstraints ++ (opsTypes.map (·.2)).flatten)
end

/--
  Collect the final type with metavariables
  and all the constraints on those metavariables.
-/
def collectConstraints (σ : OpSignature') (e : Computation) :
    Except String (ComputationTy' × Constraints) :=
  collectCompConstraints σ [] e |>.run' {} |>.run

mutual
/--
  Substitute `.mvar n` with the value type `new`
  anywhere in the computation type.
-/
def substMVarComp (n : Nat) (new : ValueTy') : ComputationTy' → ComputationTy'
| ⟨returnTy⟩ => ⟨substMVarVal n new returnTy⟩

/--
  Substitute `.mvar n` with the value type `new`
  anywhere in the value type.
-/
def substMVarVal (n : Nat) (new : ValueTy') : ValueTy' → ValueTy'
| .mvar n' => if n = n' then new else .mvar n'
| .function input output => .function (substMVarVal n new input) (substMVarComp n new output)
| .handler c1 c2 => .handler (substMVarComp n new c1) (substMVarComp n new c2)
| .bool => .bool
end

mutual
/--
  Check if `.mvar n` appears anywhere in the given value type.
-/
def mvarInVal (n : Nat) : ValueTy' → Bool
| .mvar n' => n == n'
| .function input output => mvarInVal n input || mvarInComp n output
| .handler c1 c2 => mvarInComp n c1 || mvarInComp n c2
| .bool => false

/--
  Check if `.mvar n` appears anywhere in the given computation type.
-/
def mvarInComp (n : Nat) : ComputationTy' → Bool
| ⟨returnTy⟩ => mvarInVal n returnTy
end

/--
  Apply the value type substitution function `f` to the constraint.
-/
def Constraint.applySubst (f : ValueTy' → ValueTy') : Constraint → Constraint
| .valEq τ τ' => .valEq (f τ) (f τ')

/--
  Apply the value type substitution function `f` to every constraints.
-/
def List.applySubst (f : ValueTy' → ValueTy') (c : Constraints) : Constraints :=
  c.map (·.applySubst f)

/--
  Given a list of constraints, construct a substitution to solve them.
-/
def unify : Constraints → Option (ComputationTy' → ComputationTy')
| [] => some id
| .valEq τ τ' :: cs => do
  if τ = τ' then
    return ←unify cs
  else if let .mvar n := τ then
    if ¬mvarInVal n τ' then
      let compSub := substMVarComp n τ'
      let valSub := substMVarVal n τ'
      let unifySubCs ← unify (cs.applySubst valSub)
      return unifySubCs ∘ compSub
  else if let .mvar n := τ' then
    if ¬mvarInVal n τ then
      let compSub := substMVarComp n τ
      let valSub := substMVarVal n τ
      let unifySubCs ← unify (cs.applySubst valSub)
      return unifySubCs ∘ compSub
  else if let .function τ₀ τ₁ := τ then
    if let .function τ₀' τ₁' := τ' then
      return ← unify (.valEq τ₀ τ₀' :: .valEq (τ₁.returnTy) (τ₁'.returnTy) :: cs)
  none
partial_fixpoint

/--
  Infer the type of the computation `c` given the operation signature `σ`.
-/
def inferCompType (σ : OpSignature) (c : Computation) : Except String ComputationTy' :=
  match collectConstraints σ c with
  | .ok (type, constraints) =>
    if let some substitution := unify constraints then
      Except.ok (substitution type)
    else
      Except.error s!"Failed to unify constraints {repr constraints}"
  | .error e => .error e

/--
  Infer the type of the value `v` given the operation signature `σ`.
-/
def inferValType (σ : OpSignature) (v : Value) : Except String ValueTy' := (do
  let (type, constraints) ← collectCompConstraints σ {} (Computation.ret v)
  if let some substitution := unify constraints then
    return (substitution type).returnTy
  else
    Except.error s!"Failed to unify constraints {repr constraints}")
  |>.run' {} |>.run

open Input
#eval inferCompType (Std.TreeMap.ofList [("print", (ValueTy.bool, ValueTy.bool))]) {{{
  with handler {ops := []} handle
  (fun x ↦ return 1) True
}}}
