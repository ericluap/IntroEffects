import IntroEffects.Expr

/-!
  Basic functions for open and closing binders
  with the locally nameless representation.
-/

/-
  Define the functions that replace free variables
  with dangling bound variables
-/
mutual
/--
  Replace every free variable whose name is `me`
  with a dangling bound variable pointing at `level`.
-/
def abstractValueLvl (me : Name) (level : Nat) : Value → Value
| .var (.fvar you) => if you = me then .var (.bvar level) else .var (.fvar you)
| .lam comp => .lam <| abstractComputationLvl me (level+1) comp
| .hdl h => .hdl <| abstractHandlerLvl me level h
| .pair v₁ v₂ => .pair (abstractValueLvl me level v₁) (abstractValueLvl me level v₂)
| .string s => .string s
| .bool b => .bool b
| .unit => .unit
| .var (.bvar b) => .var (.bvar b)
termination_by v => sizeOf v
decreasing_by
  all_goals simp
  all_goals grind

/--
  Replace every free variable whose name is `me`
  with a dangling bound variable pointing at `level`.
-/
def abstractComputationLvl (me : Name) (level : Nat) : Computation → Computation
| .ret v => .ret (abstractValueLvl me level v)
| .opCall op v c => .opCall op (abstractValueLvl me level v) (abstractComputationLvl me (level+1) c)
| .bind c₁ c₂ => .bind (abstractComputationLvl me level c₁) (abstractComputationLvl me (level+1) c₂)
| .ite v c₁ c₂ => .ite (abstractValueLvl me level v) (abstractComputationLvl me level c₁) (abstractComputationLvl me level c₂)
| .app v₁ v₂ => .app (abstractValueLvl me level v₁) (abstractValueLvl me level v₂)
| .handle v c => .handle (abstractValueLvl me level v) (abstractComputationLvl me level c)
| .join v₁ v₂ => .join (abstractValueLvl me level v₁) (abstractValueLvl me level v₂)
| .fst v => .fst (abstractValueLvl me level v)
| .snd v => .snd (abstractValueLvl me level v)
termination_by c => sizeOf c
decreasing_by
  all_goals simp
  all_goals grind

def abstractOps (me : Name) (level : Nat) : List OpClause → List OpClause
| [] => []
| ⟨op, body⟩ :: ls =>
  ⟨op, abstractComputationLvl me (level+2) body⟩ :: abstractOps  me level ls
termination_by l => sizeOf l

/--
  Replace every free variable whose name is `me`
  with a dangling bound variable pointing at `level`.
-/
def abstractHandlerLvl (me : Name) (level : Nat) : Handler → Handler
| ⟨some ret, ops'⟩ =>
    ⟨some (abstractComputationLvl me (level+1) ret), abstractOps me level ops'⟩
| ⟨none, ops'⟩ =>
  ⟨none, abstractOps me level ops'⟩
termination_by h => sizeOf h
decreasing_by
  all_goals simp
  all_goals grind

end

/-
  Replace every dangling bound variable pointing at `level`
  with the value `what
-/
mutual

/--
  Replace every dangling bound variable pointing at `level`
  with the value `what
-/
def instantiateValueLvl (what : Value) (level : Nat) : Value → Value
| var@(.var (.bvar bvarLevel)) => if bvarLevel = level then what else var
| .lam c => .lam <| instantiateComputationLvl what (level + 1) c
| .hdl h => .hdl <| instantiateHandlerLvl what level h
| .pair v₁ v₂ => .pair (instantiateValueLvl what level v₁) (instantiateValueLvl what level v₂)
| .string s => .string s
| .bool b => .bool b
| .unit => .unit
| .var v => .var v
termination_by v => sizeOf v
decreasing_by
  all_goals simp
  all_goals grind

/--
  Replace every dangling bound variable pointing at `level`
  with the value `what
-/
def instantiateComputationLvl (what : Value) (level : Nat) : Computation → Computation
| .ret v => .ret <| instantiateValueLvl what level v
| .opCall op v c => .opCall op (instantiateValueLvl what level v) (instantiateComputationLvl what (level+1) c)
| .bind c₁ c₂ => .bind (instantiateComputationLvl what level c₁) (instantiateComputationLvl what (level+1) c₂)
| .ite v c₁ c₂ => .ite (instantiateValueLvl what level v) (instantiateComputationLvl what level c₁) (instantiateComputationLvl what level c₂)
| .app v₁ v₂ => .app (instantiateValueLvl what level v₁) (instantiateValueLvl what level v₂)
| .handle v c => .handle (instantiateValueLvl what level v) (instantiateComputationLvl what level c)
| .join v₁ v₂ => .join (instantiateValueLvl what level v₁) (instantiateValueLvl what level v₂)
| .fst v => .fst (instantiateValueLvl what level v)
| .snd v => .snd (instantiateValueLvl what level v)
termination_by c => sizeOf c
decreasing_by
  all_goals simp
  all_goals grind

def instantiateOps (what : Value) (level : Nat) : List OpClause → List OpClause
| [] => []
| ⟨op, body⟩ :: ls =>
  ⟨op, instantiateComputationLvl what (level+2) body⟩ :: instantiateOps what level ls
termination_by l => sizeOf l

/--
  Replace every dangling bound variable pointing at `level`
  with the value `what
-/
def instantiateHandlerLvl (what : Value) (level : Nat) : Handler → Handler
| ⟨some ret, ops'⟩ =>
    ⟨some (instantiateComputationLvl what (level+1) ret), instantiateOps what level ops'⟩
| ⟨none, ops'⟩ =>
  ⟨none, instantiateOps what level ops'⟩
termination_by h => sizeOf h
decreasing_by
  all_goals simp
  all_goals grind

end

/--
  Replace every dangling bound variable referring
  to the first dangling depth with `what`
-/
def instantiateComp (what : Value) (comp : Computation) : Computation :=
  instantiateComputationLvl what 0 comp
