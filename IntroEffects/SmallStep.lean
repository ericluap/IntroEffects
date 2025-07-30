import IntroEffects.LocallyNameless

/-!
  Define the small step operational semantics
  and prove its determinism.
-/

/--
  Returns the `OpClause` with name `name`.

  Recall that the body of an `OpClause` has two dangling bvars.
-/
def Handler.lookup (hdl : Handler) (name : Name) :=
  hdl.ops.find? (·.op == name)

/--
  Assuming that `body` has two dangling bvars,
  we replace the inner bvar with `cont`
  and the outer bvar with `arg`.
-/
def instantiate2 (arg cont : Value) (body : Computation) : Computation :=
  instantiateComputationLvl arg 1 (instantiateComputationLvl cont 0 body)

def strAppend : String → String → String
| "", s => s
| s, "" => s
| s₁, s₂ => s₁ ++ " " ++ s₂

/--
  The small step operational semantics
-/
@[grind cases]
inductive Step : Computation → Computation → Prop
/-- `(λx. body) v ⤳ body[v/x]`

    Since `body` is assumed to have one dangling bvar,
    we instantiate it with `v` to get the substitution.
 -/
| beta v body : Step (.app (.lam body) v) (instantiateComp v body)
/-- `(recfun f x. body) v ⤳ body[recfun f x. body/f, v/x]

  Since `body` is assumed to have two dangling bvars,
  we replace the outermost one with a reference to the function itself
  and the inner one with the given argumetn `v`.
-/
| recBeta v body : Step (.app (.recfun body) v) (instantiate2 (.recfun body) v body)
/-- `if True then c₁ else c₂ ⤳ c₁` -/
| iteTrue c₁ c₂ : Step (.ite (.bool true) c₁ c₂) c₁
/-- `if False then c₁ else c₂ ⤳ c₂` -/
| iteFalse c₁ c₂ : Step (.ite (.bool false) c₁ c₂) c₂
/--  If `c₁ ⤳ c₁'`, then `do x ← c₁ in c₂ ⤳ do x ← c₁' in c₂` -/
| bindStep c₁ c₁' c₂ (h : Step c₁ c₁') : Step (.bind c₁ c₂) (.bind c₁' c₂)
/-- `do x ← return v in c ⤳ c[v/x]`

    Since `c` is the second argument to bind,
    we assume that it has one dangling bvar
    and so we instantiate it with `v` to get the substitution.
-/
| bindReturn v c : Step (.bind (.ret v) c) (instantiateComp v c)
/-- `do x ← op(v; y.body) in c ⤳ op(v; y. do x ← body in c)`-/
| bindOp op v body c : Step (.bind (.opCall op v body) c) (.opCall op v (.bind body c))
/-- If `c₁ ⤳ c₂`, then `with h handle c₁ ⤳ with h handle c₂` -/
| handleInner h c₁ c₂ (h₁ : Step c₁ c₂) : Step (.handle (.hdl h) c₁) (.handle (.hdl h) c₂)
/-- `with h handle (return v) ⤳ retBody[v/x]`

    Since `retBody` is the return clause of a handler,
    we assume that it has one dangling bvar
    and so we instantiate it with `v` to get the substitution.
-/
| handleReturn h v :
  Step (.handle (.hdl h) (.ret v)) (instantiateComp v h.ret)
/-- `with h handle op(v; y.body) ⤳ c[v/x, (y ↦ with h handle body)/k]`

    Since `c` is the body of an `OpClause`,
    we assume it has two dangling bvars
    and so use `instantiateOpClauseBody` to do the two substitutions.
    And note that since `body` is the body of an `opCall`,
    we assume it has one dangling bvar
    and so we can place it in a lambda without needing to do anything.
-/
| handleOpHit h op v body c (hop : h.lookup op = some ⟨op, c⟩) :
  Step (.handle (.hdl h) (.opCall op v body))
    (instantiate2 v (.lam (.handle (.hdl h) body)) c)
/-- `with h handle op(v; y.body) ⤳ op(v; y. with h handle body)`

    Since `body` is the body of an `opCall`,
    we assume it has a dangling bvar
    and so `with h handle body` also has a dangling bvar
    which means no substitution or instantiating is needed.
-/
| handleOpMiss h op v body (hop : h.lookup op = none) :
  Step (.handle (.hdl h) (.opCall op v body)) (.opCall op v (.handle (.hdl h) body))
/--
  `join s₁ s₂ ⤳ return (str(strAppend s₁ s₂))`
-/
| join s₁ s₂ : Step (.join (.string s₁) (.string s₂)) (.ret (.string (strAppend s₁ s₂)))
/--
  `fst pair(v₁, v₂) ⤳ return v₁`
-/
| fstStep v₁ v₂ : Step (.fst (.pair v₁ v₂)) (.ret v₁)
/--
  `snd pair(v₁, v₂) ⤳ return v₂`
-/
| sndStep v₁ v₂ : Step (.snd (.pair v₁ v₂)) (.ret v₂)
| add v₁ v₂ : Step (.add (.num v₁) (.num v₂)) (.ret (.num (v₁ + v₂)))
| sub v₁ v₂ : Step (.sub (.num v₁) (.num v₂)) (.ret (.num (v₁ - v₂)))
| max v₁ v₂ : Step (.max (.num v₁) (.num v₂)) (.ret (.num (Max.max v₁ v₂)))
| lt v₁ v₂ : Step (.lt (.num v₁) (.num v₂)) (.ret (.bool (v₁ < v₂)))
| mul v₁ v₂ : Step (.mul (.num v₁) (.num v₂)) (.ret (.num (v₁ * v₂)))
| eq v₁ v₂ : Step (.eq v₁ v₂) (.ret (.bool (v₁ == v₂)))
infix:50 " ⤳ " => Step

/--
  If `c` can be step reduced,
  then there is only one computation it can reduced to.
-/
theorem step_determinism (c c₁ c₂ : Computation) (c_step_c₁ : c ⤳ c₁)
    (c_step_c₂ : c ⤳ c₂) : c₁ = c₂ := by
  induction c_step_c₁ generalizing c₂ <;> grind

@[grind cases]
inductive StepStar : Computation → Computation → Prop
| refl (c) : StepStar c c
| trans : Step c₁ c₂ → StepStar c₂ c₃ → StepStar c₁ c₃

infix:50 " ⤳⋆ " => StepStar
