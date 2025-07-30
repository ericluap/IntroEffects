import IntroEffects.Type
import IntroEffects.Syntax
import Batteries.Data.List

inductive PossibleOps where
| names : List String → PossibleOps
| mvar : Nat → PossibleOps

mutual

/--
  The possible types for a value.
-/
inductive ValueTy' where
| bool
| function : ValueTy' → ComputationTy' → ValueTy'
| handler : ComputationTy' → ComputationTy' → ValueTy'
| mvar : Nat → ValueTy'

/--
  The type of a computation is the type of the value it returns
  as well as the operations it can possibly call.
-/
structure ComputationTy' where
  returnTy : ValueTy'
  Δ : List String
end

/--
  A constraint says that two types must be equal.
  This constrains what actual types a metavariable couuld have.
-/
inductive Constraint where
| valEq (τ τ' : ValueTy') -- `τ ≡ τ'`
--| possibleOpsEq (p p' : PossibleOps)
| compEq (c c' : ComputationTy')
--| hasOp (p : PossibleOps) (op : String)

abbrev Ctx' := List ValueTy'
abbrev OpSignature' := Std.TreeMap String (ValueTy' × ValueTy')
abbrev Constraints := List Constraint

structure MVarState where
  next : Nat := 0

abbrev MetaM := ExceptT String (StateM MVarState)

def freshValueMVar : MetaM ValueTy' := do
  let n ← get <&> (·.next)
  modify (fun s => {next := s.next + 1})
  return (.mvar n)

--def fresh

def freshCompMVar : MetaM ComputationTy' := do
  return ({returnTy := ←freshValueMVar, Δ := []})

mutual
partial def collectValConstraints (σ : OpSignature') (Γ : Ctx') :
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

partial def collectCompConstraints (σ : OpSignature') (Γ : Ctx') :
    Computation → MetaM (ComputationTy' × Constraints)
| .ret v => do
  let (τ, C) ← collectValConstraints σ Γ v
  return (.mk τ [], C)
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
  return ({returnTy := τ_cont.returnTy, Δ := τ_cont.Δ.insert name},
    newConstraints ++ C_v ++ C_cont)
| .bind c1 c2 => do
  let (τ_c1, C_c1) ← collectCompConstraints σ Γ c1

  -- `c2` has one dangling bvar
  let α ← freshValueMVar
  let (τ_c2, C_c2) ← collectCompConstraints σ (α :: Γ) c2

  return ({returnTy := τ_c2.returnTy, Δ := τ_c1.Δ ∪ τ_c2.Δ}, C_c1 ++ C_c2)
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
  return ({returnTy := τ1.returnTy, Δ := τ1.Δ ∪ τ2.Δ},
    newConstraints ++ C1 ++ C2 ++ Cb)
| .handle h c => do
  let (.handler startType endType, Ch) ← collectValConstraints σ Γ h
    | Except.error s!"Expected a handler but was given {h}"
  let (τc, Cc) ← collectCompConstraints σ Γ c
  let newConstraints : Constraints := [.compEq startType τc]
  return (endType, newConstraints ++ Ch ++ Cc)
| c => Except.error s!"Unsupported computation {c}"

partial def collectOpClauseConstraints (σ : OpSignature') (Γ : Ctx') :
    OpClause → MetaM (ComputationTy' × Constraints)
| ⟨op, body⟩ => do
  let some (Aop, Bop) := (σ.get? op) | Except.error s!"Unknown op {op}"

  -- `body` has two dangling bvars
  let α ← freshValueMVar
  let β ← freshValueMVar
  let (τ_body, C_body) ← collectCompConstraints σ (α :: β :: Γ) body

  let newConstraints := [
    .valEq α (.function )
  ]
  return ()

partial def collectHandlerConstraints (σ : OpSignature') (Γ : Ctx') :
    Handler → MetaM (ValueTy' × Constraints)
| ⟨ret, ops⟩ => do
  -- `ret` has one dangling bvar
  let α ← freshValueMVar
  let (τret, Cret) ← collectCompConstraints σ (α :: Γ) ret
  let opsTypes ← ops.mapM (collectOpClauseConstraints σ Γ ·)
  return ()
end

/-
inductive CTHasType (σ : OpSignature) : Ctx → Expr → Ty → List Constraints → Prop where
/--
 If `(x : A) ∈ Γ` then `Γ ⊢ x : A ▸ ∅`
-/
| var x A : ((x : A) ∈ Γ) → CTHasType σ Γ (Value.var (.bvar x)) A []
/--
  `Γ ⊢ True : bool` and `Γ ⊢ False : bool ▸ ∅` with no const
-/
| bool b : CTHasType σ Γ (Value.bool b) ValueTy.bool []
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
-/
