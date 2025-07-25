import IntroEffects.SmallStep

/-!
  Define an `eval` function and `#evalLang` commmand
  that are proven to match the small step operational semantics.
-/

/--
  Reduces a computation by a single step.
-/
def evalSingleStep : Computation → Option Computation
/- `(λx. body) v → body[v/x]`

    Since `body`is assumed to have one dangling bvar,
    we instantiate it with `v` to get the substitution.
 -/
| .app (.lam body) v => some <| instantiateComp v body
| .ite (.bool true) c₁ _ => some c₁
| .ite (.bool false) _ c₂ => some c₂
/- `do x ← return v in c → c[v/x]`

    Since `c` is the second argument to bind,
    we assume that it has one dangling bvar
    and so we instantiate it with `v` to get the substitution.
-/
| .bind (.ret v) c => some <| instantiateComp v c
/- `do x ← op(v; y.body) in c → op(v; y. do x ← body in c)`

    Since `body` is the computation in `opCall`,
    we assume that it has one dangling bvar
    and so we can just pass it to `bind`
-/
| .bind (.opCall op v body) c => some <| .opCall op v (.bind body c)
| .bind c₁ c₂ => (evalSingleStep c₁).map (fun c₁' => .bind c₁' c₂)
| .handle (.hdl h) (.ret v) =>
  match h.ret? with
  /- `with h handle (return v) → retBody[v/x]`

    Since `retBody` is the return clause of a handler,
    we assume that it has one dangling bvar
    and so we instantiate it with `v` to get the substitution.
-/
  | some retBody => some <| instantiateComp v retBody
  | none => some <| .ret v
| .handle (.hdl h) (.opCall op v body) =>
  match h.lookup op with
  /- `with h handle op(v; y.body) → c[v/x, (y ↦ with h handle body)/k]`

    Since `c` is the body of an `OpClause`,
    we assume it has two dangling bvars
    and so use `instantiateOpClauseBody` to do the two substitutions.
    And note that since `body` is the body of an `opCall`,
    we assume it has one dangling bvar
    and so we can place it in a lambda without needing to do anything.
  -/
  | some ⟨_, c⟩ =>
    let cont := .lam (.handle (.hdl h) body)
    some <| instantiateOpClauseBody v cont c
  /- `with h handle op(v; y.body) → op(v; y. with h handle body)`

    Since `body` is the body of an `opCall`,
    we assume it has a dangling bvar
    and so `with h handle body` also has a dangling bvar
    which means no substitution or instantiating is needed.
-/
  | none => some <| .opCall op v (.handle (.hdl h) body)
| .handle (.hdl h) c =>
  (evalSingleStep c).map (fun c' => .handle (.hdl h) c')
| .join (.string s₁) (.string s₂) => some <| .ret (.string (s₁ ++ " " ++ s₂))
| _ => none

/--
  If `evalSingleStep` reduces `c` to `c'`,
  then `c ⤳ c'`.
-/
theorem evalSingleStep_sound {c c' : Computation} :
    evalSingleStep c = some c' → c ⤳ c' := by
  cases c with
  | ret => simp [evalSingleStep]
  | app fn arg =>
    cases fn <;> simp [evalSingleStep]
    · intro h
      rw [←h]
      solve_by_elim
  | opCall => simp [evalSingleStep]
  | ite v =>
    cases v <;> try simp [evalSingleStep]
    next a =>
      cases a <;> (
      simp [evalSingleStep]
      intro h
      rw [←h]
      solve_by_elim)
  | bind c₁ c₂ =>
    cases h₁ : evalSingleStep c₁ with
    | none =>
      cases c₁ <;> simp [evalSingleStep, h₁] <;>
      ( intro h
        rw [←h]
        solve_by_elim)
    | some c₁' =>
      intro h
      have step : c₁ ⤳ c₁' := evalSingleStep_sound h₁
      have := Step.bindStep _ _ c₂ step
      cases c₁ <;> simp [evalSingleStep] at h
      all_goals grind
  | handle v body =>
    cases v with
    | hdl h =>
      cases body with
      | ret r =>
        cases h with
        | mk ret? ops' =>
          cases ret? <;>
          ( simp [evalSingleStep]
            intro h; rw [←h]
            solve_by_elim)
      | opCall op v cont =>
        cases hlookup : h.lookup op with
        | some clause =>
          cases clause with
          | mk name ops' =>
            simp [evalSingleStep, hlookup]
            have := List.find?_some hlookup
            simp at this
            rw [this] at hlookup
            intro eq; rw [←eq]
            apply Step.handleOpHit
            exact hlookup
        | none =>
          simp [evalSingleStep, hlookup]
          intro h; rw [←h]
          solve_by_elim
      | handle | bind | ite | app =>
        simp [evalSingleStep]
        intro x eq1 eq2
        rw [←eq2]
        apply Step.handleInner
        apply evalSingleStep_sound
        assumption
      | join =>
        simp [evalSingleStep]
        intro x h1 h2
        have := evalSingleStep_sound h1
        rw [←h2]
        exact Step.handleInner h _ _ this
    | _ => simp [evalSingleStep]
  | join v1 v2 =>
    cases v1 <;> cases v2 <;> simp [evalSingleStep]
    · intro h
      rw [←h]
      constructor

/--
  If `c ⤳ c'`, then `evalSingleStep` reduces `c` to `c'`.
-/
theorem evalSingleStep_complete {c c' : Computation} :
    c ⤳ c' → evalSingleStep c = (some c') := by
  intro h
  cases h <;> try grind [evalSingleStep]
  next c₁ c₁' c₂ h =>
    have := evalSingleStep_complete h
    cases c₁ <;> grind [evalSingleStep]
  next hdl c₁ c₂ h =>
    have := evalSingleStep_complete h
    cases c₁ <;> grind [evalSingleStep]

/--
  `evalSingleStep` reduces `c` to `c'` if and only if
  `c ⤳ c'`
-/
theorem evalSingleStep_iff_step (c c' : Computation) :
    evalSingleStep c = some c' ↔ c ⤳ c' :=
  ⟨evalSingleStep_sound, evalSingleStep_complete⟩

/--
  Evaluate the computation with a maximum number of steps.
-/
def evalFuel : Nat → Computation → Option Value
| 0, _ => none
| _+1, .ret v => some v
| n+1, c =>
  match evalSingleStep c with
  | some c' => evalFuel n c'
  | none => none

/--
  Evaluate the computation (no maximum number of steps)
-/
def eval : Computation → Option Value
| .ret v => some v
| c =>
  match evalSingleStep c with
  | some c' => eval c'
  | none => none
partial_fixpoint

/--
  If `evalFuel` reduces `c` to `ret v` within `n` steps,
  then `c ⤳⋆ ret v`.
-/
theorem evalFuel_sound  : evalFuel n c = some v → c ⤳⋆ .ret v := by
  induction h : n generalizing c with
  | zero => simp [evalFuel]
  | succ n ih =>
    cases hstep : evalSingleStep c with
    | none =>
      cases c <;> try grind [evalFuel]
      · simp [evalFuel]
        intro h; rw [←h]; constructor
    | some c' =>
      cases c with
      | ret v =>
        simp [evalFuel]
        intro h; rw [←h]; constructor
      | _ =>
        simp [evalFuel, hstep]
        intro h
        exact StepStar.trans (evalSingleStep_sound hstep) (evalFuel_sound h)

/--
  If there exists an `n` such that `evalFuel` reduces `c` to `v`
  within `n` steps, then `c ⤳⋆ .ret v`.
-/
theorem evalFuel_soundExists : (∃n, evalFuel n c = some v) → c ⤳⋆ .ret v := by
  intro h
  obtain ⟨n, hn⟩ := h
  exact evalFuel_sound hn

/--
  If `c ⤳ c'`, then `evalFuel` reduces `c` within `n+1` steps
  to the same thing that `evalFuel` reduces `c'` within `n` steps.
-/
theorem evalFuel_step (h : c ⤳ c') : evalFuel (n + 1) c = evalFuel n c' := by
  have := evalSingleStep_complete h
  cases c <;> grind [evalFuel]

theorem evalFuel_complete_aux (h : c ⤳⋆ r) :
    ∀v, r = .ret v → ∃n, evalFuel n c = some v := by
  induction h with
  | refl c' =>
    intro v hv
    cases hv
    exact ⟨1, by simp [evalFuel]⟩
  | @trans c1 c2 c3 hStep hTail ih =>
    intro v hv
    obtain ⟨n, ihFuel⟩ := ih v hv
    refine ⟨n+1, ?_⟩
    simp [evalFuel_step hStep, ihFuel]

/--
  If `c ⤳⋆ .ret v`, then for some `n`,
  `evalFual` reduces `c` to `v` within `n` steps.
-/
theorem evalFuel_complete (h : c ⤳⋆ .ret v) :
    ∃n, evalFuel n c = some v := evalFuel_complete_aux h v rfl

/--
  There exists an `n` such that `evalFuel` reduces
  `c` to `v` within `n` steps if and only if
  `c ⤳⋆ .ret v`.
-/
theorem evalFuel_iff_stepStar :
    (∃n, evalFuel n c = some v) ↔ c ⤳⋆ .ret v :=
  ⟨evalFuel_soundExists, evalFuel_complete⟩

/--
  If `evalFuel` reduces `c` to `v` within `n` steps,
  then `eval` reduces `c` to `v`.
-/
theorem evalFuel_to_eval :
    evalFuel n c = some v → eval c = some v := by
  induction n generalizing c with
  | zero => simp [evalFuel]
  | succ n ih =>
    cases hstep : evalSingleStep c with
    | none =>
      cases c with
      | ret _ => simp [evalFuel, eval]
      | _ => simp [evalFuel, eval, hstep]
    | some c' =>
      intro hFuel
      have : evalFuel n c' = some v := by
        cases c <;> try simpa [evalFuel, hstep] using hFuel
        · simp [evalSingleStep] at hstep
      have : eval c' = some v := ih this
      cases c <;> grind [evalFuel, eval]

/--
  If there exists an `n` such that `evalFuel` reduces `c` to `v`
  within `n` steps, then `eval` reduces `c` to `v`.
-/
theorem evalFuelExists_to_eval :
    (∃n, evalFuel n c = some v) → eval c = some v := by
  intro h
  obtain ⟨n, hn⟩ := h
  exact evalFuel_to_eval hn

attribute [elab_as_elim] eval.partial_correctness
/--
  If `eval` reduces `c` to `v`, there exists an `n`
  such that `evalFuel` reduces `c` to `v` within `n` steps.
-/
theorem eval_to_evalFuelExists :
    eval c = some v → (∃n, evalFuel n c = some v) := by
  intro h
  refine eval.partial_correctness _ ?_ c  v h
  · intro eval' ih c' v' h'
    split at h'
    next => exists 1
    split at h'
    next h'' =>
      obtain ⟨n, hn⟩ := ih _ _ h'
      exists n + 1
      simp [evalFuel, h'', hn]
    next => simp at h'

/--
  `eval` reduces `c` to `v` if and only if
  for some `n`, `evalFuel` reduces `c` to `v` within `n` steps.
-/
theorem eval_iff_evalFuel :
    eval c = some v ↔ ∃n, evalFuel n c = some v := by
  constructor
  · exact fun a => eval_to_evalFuelExists a
  · exact fun a => evalFuelExists_to_eval a

/--
  `eval` reduces `c` to `v` if and only if
  `c ⤳⋆ .ret v`
-/
theorem eval_iff_stepStar :
    eval c = some v ↔ c ⤳⋆ .ret v :=
  eval_iff_evalFuel.trans evalFuel_iff_stepStar

macro "#evalLang " e:term : command =>
  `(#eval (eval $e).getD (.var (.fvar "Error")))
