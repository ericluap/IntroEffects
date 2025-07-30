import IntroEffects.Type
import IntroEffects.Syntax
import Batteries.Data.List

/-!
  Defines the function `inferType`
  for inferring the types of computations and values.
-/

mutual

/--
  The possible types for a value.
  This is the same as `ValueTy` but with metavariables.
-/
inductive ValueTy' where
| bool | string | num | unit | void
| pair : ValueTy' → ValueTy' → ValueTy'
| function : ValueTy' → ComputationTy' → ValueTy'
| handler : ComputationTy' → ComputationTy' → ValueTy'
| mvar : Nat → ValueTy'
deriving Repr, DecidableEq, Inhabited

/--
  The type of a computation is the type of the value it returns.
-/
structure ComputationTy' where
  returnTy : ValueTy'
deriving Repr, DecidableEq
end

mutual
/--
  Check if `.mvar n` appears anywhere in the given value type.
-/
def mvarInVal (n : Nat) : ValueTy' → Bool
| .mvar n' => n == n'
| .function input output => mvarInVal n input || mvarInComp n output
| .handler c1 c2 => mvarInComp n c1 || mvarInComp n c2
| .pair v1 v2 => mvarInVal n v1 || mvarInVal n v2
| .bool => false
| .unit => false
| .string => false
| .num => false
| .void => false

/--
  Check if `.mvar n` appears anywhere in the given computation type.
-/
def mvarInComp (n : Nat) : ComputationTy' → Bool
| ⟨returnTy⟩ => mvarInVal n returnTy
end

/--
  A constraint says that two types must be equal.
  This constrains what actual types a metavariable couuld have.
-/
inductive Constraint where
| valEq (τ τ' : ValueTy') -- `τ ≡ τ'`
deriving Repr, Inhabited

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
| .bool => .bool | .unit => .unit | .num => .num | .string => .string | .void => .void
| .pair v1 v2 => .pair (valueTyToPrime v1) (valueTyToPrime v2)
| .handler c1 c2 => .handler (compTyToPrime c1) (compTyToPrime c2)
| .function v c => .function (valueTyToPrime v) (compTyToPrime c)

def compTyToPrime : ComputationTy → ComputationTy'
| ⟨returnTy, _⟩ => ⟨valueTyToPrime returnTy⟩
end

def mvarInConstraint (n : Nat) : Constraint → Bool
| .valEq v1 v2 => mvarInVal n v1 || mvarInVal n v2
def mvarInConstraints (n : Nat) (cs : Constraints) := cs.any (mvarInConstraint n ·)

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
| .recfun body => do
  -- Since `body` has two dangling bvars
  let α ← freshValueMVar
  let β ← freshValueMVar
  let (k, C) ← collectCompConstraints σ (α :: β :: Γ) body
  let newConstraints : Constraints := [.valEq β (.function α k)]
  return (.function α k, newConstraints ++ C)
| .pair v1 v2 => do
  let (τ1, C1) ← collectValConstraints σ Γ v1
  let (τ2, C2) ← collectValConstraints σ Γ v2
  return (.pair τ1 τ2, C1 ++ C2)
| .string _ => pure (.string, [])
| .num _ => pure (.num, [])
| .unit => pure (.unit, [])
| .var (.fvar n) => Except.error s!"Free variable {n}"

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
  let (τ_c1, C_c1) ← collectCompConstraints σ Γ c1

  -- `c2` has one dangling bvar
  let α ← freshValueMVar
  let (τ_c2, C_c2) ← collectCompConstraints σ (α :: Γ) c2

  let newConstraints : Constraints := [.valEq α τ_c1.returnTy]

  return ({returnTy := τ_c2.returnTy}, newConstraints ++ C_c1 ++ C_c2)
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
| .join v1 v2 => do
  let (τ1, C1) ← collectValConstraints σ Γ v1
  let (τ2, C2) ← collectValConstraints σ Γ v2
  let newConstraints : Constraints := [
    .valEq τ1 .string,
    .valEq τ2 .string,
  ]
  return ({returnTy := .string}, newConstraints ++ C1 ++ C2)
| .fst v => do
  -- We may not know the types in the pair yet
  let α ← freshValueMVar
  let β ← freshValueMVar
  let (τ, C) ← collectValConstraints σ Γ v
  let newConstraints : Constraints := [.valEq τ (.pair α β)]
  return ({returnTy := α}, newConstraints ++ C)
| .snd v => do
  -- We may not know the types in the pair yet
  let α ← freshValueMVar
  let β ← freshValueMVar
  let (τ, C) ← collectValConstraints σ Γ v
  let newConstraints : Constraints := [.valEq τ (.pair α β)]
  return ({returnTy := β}, newConstraints ++ C)
| .add v1 v2 | .sub v1 v2 | .mul v1 v2 | .max v1 v2 => do
  let (τ1, C1) ← collectValConstraints σ Γ v1
  let (τ2, C2) ← collectValConstraints σ Γ v2
  let newConstraints : Constraints := [
    .valEq τ1 .num,
    .valEq τ2 .num
  ]
  return ({returnTy := .num}, newConstraints ++ C1 ++ C2)
| .lt v1 v2 => do
  let (τ1, C1) ← collectValConstraints σ Γ v1
  let (τ2, C2) ← collectValConstraints σ Γ v2
  let newConstraints : Constraints := [
    .valEq τ1 .num,
    .valEq τ2 .num
  ]
  return ({returnTy := .bool}, newConstraints ++ C1 ++ C2)
| .eq v1 v2 => do
  let (_, C1) ← collectValConstraints σ Γ v1
  let (_, C2) ← collectValConstraints σ Γ v2
  return ({returnTy := .bool}, C1 ++ C2)

def collectOpClauseConstraints (σ : OpSignature') (Γ : Ctx') :
    OpClause → MetaM (ComputationTy' × Constraints)
| ⟨op, body⟩ => do
  let some (Aop, Bop) := (σ.get? op) | Except.error s!"Unknown op {op}"

  -- `body` has two dangling bvars
  let α ← freshValueMVar
  let (τ_body, C_body) ← collectCompConstraints σ (α :: Aop :: Γ) body

  -- The only place `void` can be introduced is in the op signature
  -- We make sure it is used correctly.
  if Aop = .void then
    Except.error s!"Operation {op} has input type void."
  if Bop = .void then
    match α with
    | .mvar n =>
      if mvarInComp n τ_body || mvarInConstraints n C_body then
        Except.error s!"Operation {op} has return type void but uses its continuation."
    | _ => Except.error "Created mvar is not an mvar??"

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
| .pair v1 v2 => .pair (substMVarVal n new v1) (substMVarVal n new v2)
| .bool => .bool
| .unit => .unit
| .string => .string
| .num => .num
| .void => .void
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
partial def unify : Constraints → Except String (ComputationTy' → ComputationTy')
| [] => Except.ok id
| .valEq τ τ' :: cs => do
  if τ = τ' ∨ τ = .void ∨ τ' = .void then
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
  else if let .pair τ₀ τ₁ := τ then
    if let .pair τ₀' τ₁' := τ' then
      return ← unify (.valEq τ₀ τ₀' :: .valEq τ₁ τ₁' :: cs)
  Except.error s!"Failed to solve constraint {repr (Constraint.valEq τ τ')}"

/--
  Infer the type of the computation `c` given the operation signature `σ`.
-/
def inferCompType (σ : List (String × (ValueTy × ValueTy))) (c : Computation) :
    Except String ComputationTy' := do
  let (type, constraints) ← collectConstraints (Std.TreeMap.ofList σ) c
  let substitution ← unify constraints
  return substitution type

/--
  Infer the type of the value `v` given the operation signature `σ`.
-/
def inferValType (σ : List (String × (ValueTy × ValueTy))) (v : Value) :
    Except String ValueTy' := do
  let (type, constraints) ← collectConstraints (Std.TreeMap.ofList σ) (Computation.ret v)
  let substitution ← unify constraints
  return (substitution type).returnTy

/--
  The type of either a value or computation with metavariables.
-/
inductive Ty' where
| val : ValueTy' → Ty'
| comp : ComputationTy' → Ty'
/--
    Infer the type of the expression `e` given the operation signature `σ`.
-/
def inferType (σ : List (String × (ValueTy × ValueTy))) : Expr → Except String Ty'
| .val v => (.val ·) <$> inferValType σ v
| .comp c => (.comp ·) <$> inferCompType σ c

section Output
open Std (Format)
open Lean.Parser (maxPrec minPrec argPrec)

/-
  Improve the formatting of the output
-/
mutual
def ValueTy'.format (prec : Nat) : ValueTy' → Format
| .mvar n => .group <| s!"?α{n}"
| .bool => .group <| "bool"
| .handler c1 c2 => .group <| c1.format prec ++ " ⇒ " ++ c2.format prec
| .function v c => .group <| v.format prec ++ " → " ++ c.format prec
| .pair v1 v2 => .group <| "(" ++ v1.format prec ++ ", " ++ v2.format prec ++ ")"
| .void => .group <| "void"
| .unit => .group <| "unit"
| .num => .group <| "int"
| .string => .group <| "str"

def ComputationTy'.format (prec : Nat) : ComputationTy' → Format
| ⟨returnTy⟩ => .group <| "{" ++ returnTy.format prec ++ "}"
end

instance : Repr ComputationTy' where
  reprPrec comp n := comp.format n
instance : Repr ValueTy' where
  reprPrec value n := value.format n
instance : Repr Ty' where
  reprPrec e := match e with
    | .val v => reprPrec v
    | .comp c => reprPrec c

instance : ToString ComputationTy' where
  toString := toString ∘ repr
instance : ToString ValueTy' where
  toString := toString ∘ repr
instance : ToString Ty' where
  toString := toString ∘ repr

def Except.exceptFormat : Except String Ty' → String
| .ok t => toString t
| .error s => s
end Output

macro "#inferType " σ:term ", " e:term : command =>
  `(#eval (inferType $σ $e).exceptFormat)
