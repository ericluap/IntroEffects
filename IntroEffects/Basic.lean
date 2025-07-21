import Lean

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
/-- Assumes that the computation passed in has a dangling bvar -/
| lam : Computation → Value
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

/-
  Make the representations of terms nicer.
-/
section Output
open Std (Format)
open Lean.Parser (maxPrec minPrec argPrec)

/-
  Improve the formatting of the output
-/
mutual
def Value.format (prec : Nat) : Value → Format
| .var (.bvar n) => .group <| "bvar " ++ reprPrec n 0
| .var (.fvar n) => n
| .bool true => "True"
| .bool false => "False"
| .lam c => .group <| "fun " ++ .nest 2 (.line ++ c.format prec)
| .hdl h => h.format prec

def Computation.format (prec : Nat) : Computation → Format
| .ret v => .group <| "return " ++ v.format prec
| .handle h c => .group <| "with " ++ h.format prec ++ " handle" ++ .line ++ .nest 2 (c.format prec)
| .app v₁ v₂ => .group <| v₁.format prec ++ " " ++ v₂.format prec
| .ite v c₁ c₂ => .group <| "if " ++ v.format prec ++ .line ++ " then " ++
  c₁.format prec ++ .line ++ " else " ++ c₂.format prec
| .bind c₁ c₂ => .group <| "do ← " ++ c₁.format prec ++ " in " ++ .line ++ c₂.format prec
| .opCall name v c => .group <| name ++ "(" ++ v.format prec ++ "; " ++ c.format prec ++ ")"

def OpClause.format (prec : Nat) : OpClause → Format
| ⟨op, body⟩ => .group <| "{op := " ++ op ++ ", body := " ++ body.format prec ++  "}"
def Handler.format (prec : Nat) : Handler → Format
| ⟨ret?, ops⟩ =>
  .group <| "{ret? := " ++ (repr ret?) ++ ", " ++ .line ++ "ops := [" ++
    .joinSep (ops.map (·.format prec)) (", " ++ .line) ++ "]}"
where
  repr : Option Computation → Format
  | none => "none"
  | some c => c.format prec
end

instance : Repr Computation where
  reprPrec comp n := comp.format n
instance : Repr Value where
  reprPrec value n := value.format n
end Output


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
| other => other
termination_by v => sizeOf v
decreasing_by
  all_goals simp

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
| ⟨some ret, ops⟩ =>
    ⟨some (abstractComputationLvl me (level+1) ret), abstractOps me level ops⟩
| ⟨none, ops⟩ =>
  ⟨none, abstractOps me level ops⟩
termination_by h => sizeOf h
decreasing_by
  all_goals simp
  all_goals grind

end

mutual

def instantiateValueLvl (what : Value) (level : Nat) : Value → Value
| var@(.var (.bvar bvarLevel)) => if bvarLevel = level then what else var
| .lam c => .lam <| instantiateComputationLvl what (level + 1) c
| .hdl h => .hdl <| instantiateHandlerLvl what level h
| other => other
termination_by v => sizeOf v
decreasing_by
  all_goals simp

def instantiateComputationLvl (what : Value) (level : Nat) : Computation → Computation
| .ret v => .ret <| instantiateValueLvl what level v
| .opCall op v c => .opCall op (instantiateValueLvl what level v) (instantiateComputationLvl what (level+1) c)
| .bind c₁ c₂ => .bind (instantiateComputationLvl what level c₁) (instantiateComputationLvl what (level+1) c₂)
| .ite v c₁ c₂ => .ite (instantiateValueLvl what level v) (instantiateComputationLvl what level c₁) (instantiateComputationLvl what level c₂)
| .app v₁ v₂ => .app (instantiateValueLvl what level v₁) (instantiateValueLvl what level v₂)
| .handle v c => .handle (instantiateValueLvl what level v) (instantiateComputationLvl what level c)
termination_by c => sizeOf c
decreasing_by
  all_goals simp
  all_goals grind

def instantiateOps (what : Value) (level : Nat) : List OpClause → List OpClause
| [] => []
| ⟨op, body⟩ :: ls =>
  ⟨op, instantiateComputationLvl what (level+2) body⟩ :: instantiateOps what level ls
termination_by l => sizeOf l

def instantiateHandlerLvl (what : Value) (level : Nat) : Handler → Handler
| ⟨some ret, ops⟩ =>
    ⟨some (instantiateComputationLvl what (level+1) ret), instantiateOps what level ops⟩
| ⟨none, ops⟩ =>
  ⟨none, instantiateOps what level ops⟩
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

/-
  Make inputing the terms nicer
-/
section Input
open Lean Elab Term Meta

declare_syntax_cat embedded

/-- Variable reference -/
syntax:max ident : embedded
/-- Grouping of expressions -/
syntax "(" embedded ")" : embedded
/-- Application -/
syntax:arg embedded:arg embedded:max : embedded
/-- A function -/
syntax:max "fun" ident " => " embedded:arg : embedded
/-- Bool true -/
syntax "True" : embedded
/-- Bool false -/
syntax "False" : embedded
/-- Return -/
syntax "return " embedded : embedded
/-- OpCall -/
syntax ident "(" embedded "; " embedded ")" : embedded
/-- Bind -/
syntax "do " ident " ← " embedded " in " embedded : embedded
/-- If then else -/
syntax "if " embedded " then " embedded " else " embedded : embedded
/-- Handler -/
syntax "with " embedded " handle " embedded : embedded
/-- OpClause -/
syntax str "(x,k)" " ↦ " embedded : embedded
syntax "handler " "{" "return " ident " ↦ " embedded ", " "ops " " := " "[" embedded,* "]" "}" : embedded

syntax:max "~" term:max : embedded
syntax (name := embeddedTerm) "{{{" embedded "}}}" : term

/--
  A context to keep track of the
  order the bound names were introduced
-/
structure Ctx where
  bound : List Lean.Name
abbrev ElabM := StateT Ctx TermElabM

/--
  Return `some n` if `x`
  is the `n`th binder
-/
def lookup (x : Lean.Name) : Ctx → Option Nat
| ⟨bs⟩ => bs.idxOf? x


/--
  Extract the body from a lambda in syntax
-/
def extractLambdaBody : TSyntax `term → TSyntax `term
| `(term| Value.lam $body) => body
| _ => TSyntax.mk Syntax.missing

/--
  Run the continuation with the given identifier bound
-/
def withBoundIdentifier (id : Lean.Name) (cont : ElabM (TSyntax `term)) : ElabM (TSyntax `term) := do
  modify (fun ⟨bs⟩ => ⟨id :: bs⟩)
  let res ← cont
  modify (fun | ⟨_::bs⟩ => ⟨bs⟩ | ⟨[]⟩ => ⟨[]⟩)
  return res

/--
  Convert the given embedded syntax into a normal term.
-/
partial def toTermSyntax : Syntax → ElabM (TSyntax `term)
/-
  Check if the identifier has been bound already.
  Otherwise, it is a free variable.
-/
| `(embedded| $x:ident) => do
  let ctx ← get
  match lookup x.getId ctx with
  | some k => `(Value.var (Var.bvar $(Lean.quote k)))
  | none => `(Value.var (Var.fvar $(Lean.quote x.getId.toString)))
| `(embedded| True) => `(Value.bool true)
| `(embedded| False) => `(Value.bool false)
| `(embedded| ( $e )) => toTermSyntax e
| `(embedded| fun $x:ident => $body) => do
  let bodyTerm ← withBoundIdentifier x.getId (toTermSyntax body)
  `(Value.lam $bodyTerm)
| `(embedded| $f $arg) => do
  let fTerm ← toTermSyntax f
  let argTerm ← toTermSyntax arg
  `(Computation.app $fTerm $argTerm)
| `(embedded| return $e) => do
  let t ← toTermSyntax e
  `(Computation.ret $t)
| `(embedded| $op:ident ( $v ; $k )) => do
  let vTerm ← toTermSyntax v
  /-
    Extract the body of the lambda because
    `opCall` expects a computation with one dangling bvar
  -/
  let kTerm := extractLambdaBody (←toTermSyntax k)
  `(Computation.opCall $(Lean.quote op.getId.toString) $vTerm $kTerm)
| `(embedded| do $x:ident ← $c₁ in $c₂) => do
  let c₁Term ← toTermSyntax c₁
  let c₂Term ← withBoundIdentifier x.getId (toTermSyntax c₂)
  `(Computation.bind $c₁Term $c₂Term)
| `(embedded| if $v then $c₁ else $c₂) => do
  let vTerm ← toTermSyntax v
  let c₁Term ← toTermSyntax c₁
  let c₂Term ← toTermSyntax c₂
  `(Computation.ite $vTerm $c₁Term $c₂Term)
| `(embedded| with $h handle $c) => do
  let hTerm ← toTermSyntax h
  let cTerm ← toTermSyntax c
  `(Computation.handle (Value.hdl $hTerm) $cTerm)
| `(embedded| ~$e) => pure e
| `(embedded| $t:str (x,k) ↦ $e) => do
  let eTerm ← withBoundIdentifier `x (withBoundIdentifier `k (toTermSyntax e))
  `(OpClause.mk $t $eTerm)
| `(embedded| handler {return $x ↦ $e, ops := [$xs,*] }) => do
  -- Assumed to have one dangling bvar
  let eTerm ← withBoundIdentifier x.getId (toTermSyntax e)
  -- Each is assumed to have two dangling bvars
  let opsTerms ← xs.getElems.mapM (toTermSyntax ·)
  `(Handler.mk (some $eTerm) [$opsTerms,*])
| _ => pure <| TSyntax.mk Syntax.missing

@[term_elab embeddedTerm] def elabEmbedded : TermElab := fun stx _ => do
  let body := stx[1]
  let termStx ← (toTermSyntax body).run ⟨[]⟩
  elabTerm termStx.1 none
end Input

open Value Computation Handler

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
def instantiateOpClauseBody (arg cont : Value) (body : Computation) : Computation :=
  instantiateComputationLvl arg 1 (instantiateComputationLvl cont 0 body)

/--
  The small step operational semantics
-/
inductive Step : Computation → Computation → Prop
/-- `(λx. body) v ⤳ body[v/x]`

    Since `body`is assumed to have one dangling bvar,
    we instantiate it with `v` to get the substitution.
 -/
| beta v body : Step (app (lam body) v) (instantiateComp v body)
/-- `if True then c₁ else c₂ ⤳ c₁` -/
| iteTrue c₁ c₂ : Step (ite (bool true) c₁ c₂) c₁
/-- `if False then c₁ else c₂ ⤳ c₂` -/
| iteFalse c₁ c₂ : Step (ite (bool false) c₁ c₂) c₂
/--  If `c₁ ⤳ c₁'`, then `do x ← c₁ in c₂ ⤳ do x ← c₁' in c₂` -/
| bindStep c₁ c₁' c₂ (h : Step c₁ c₁') : Step (bind c₁ c₂) (bind c₁' c₂)
/-- `do x ← return v in c ⤳ c[v/x]`

    Since `c` is the second argument to bind,
    we assume that it has one dangling bvar
    and so we instantiate it with `v` to get the substitution.
-/
| bindReturn v c : Step (bind (.ret v) c) (instantiateComp v c)
/-- `do x ← op(v; y.body) in c ⤳ op(v; y. do x ← body in c)`-/
| bindOp op v body c : Step (bind (opCall op v body) c) (opCall op v (bind body c))
/-- If `c₁ ⤳ c₂`, then `with h handle c₁ ⤳ with h handle c₂` -/
| handleInner h c₁ c₂ (h₁ : Step c₁ c₂) : Step (.handle (hdl h) c₁) (.handle (hdl h) c₂)
/-- `with h handle (return v) ⤳ retBody[v/x]`

    Since `retBody` is the return clause of a handler,
    we assume that it has one dangling bvar
    and so we instantiate it with `v` to get the substitution.
-/
| handleReturn h v retBody (hr : h.ret? = some retBody) :
  Step (.handle (hdl h) (.ret v)) (instantiateComp v retBody)
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
    (instantiateOpClauseBody v (lam (.handle (.hdl h) body)) c)
/-- `with h handle op(v; y.body) ⤳ op(v; y. with h handle body)`

    Since `body` is the body of an `opCall`,
    we assume it has a dangling bvar
    and so `with h handle body` also has a dangling bvar
    which means no substitution or instantiating is needed.
-/
| handleOpMiss h op v body (hop : h.lookup op = none) :
  Step (.handle (.hdl h) (.opCall op v body)) (opCall op v (.handle (.hdl h) body))

infix:50 " ⤳ " => Step

/--
  If `c` can be step reduced,
  then there is only one computation it can reduced to.
-/
theorem step_determinism (c c₁ c₂ : Computation) (c_step_c₁ : c ⤳ c₁)
    (c_step_c₂ : c ⤳ c₂) : c₁ = c₂ := by
  induction c_step_c₁ generalizing c₂ with
  | beta => cases c_step_c₂; rfl
  | iteTrue => cases c_step_c₂; rfl
  | iteFalse => cases c_step_c₂; rfl
  | bindReturn =>
    cases c_step_c₂ with
    | bindReturn => rfl
    | bindStep _ _ _ h => cases h
  | bindOp =>
    cases c_step_c₂ with
    | bindOp => rfl
    | bindStep _ _ _ h => cases h
  | bindStep _ _ _ c₁_step_c₁' _ =>
    cases c_step_c₂ with
    | bindReturn => cases c₁_step_c₁'
    | bindStep => grind
    | bindOp => cases c₁_step_c₁'
  | handleInner _ _ _ h =>
    cases c_step_c₂ with
    | handleInner => grind
    | handleReturn => cases h
    | handleOpHit => cases h
    | handleOpMiss => cases h
  | handleReturn =>
    cases c_step_c₂ with
    | handleReturn => grind
    | handleInner _ _ _ h => cases h
  | handleOpHit =>
    cases c_step_c₂ with
    | handleOpHit => grind
    | handleInner _ _ _ h => cases h
    | handleOpMiss => grind
  | handleOpMiss =>
    cases c_step_c₂ with
    | handleOpMiss => rfl
    | handleInner _ _ _ h => cases h
    | handleOpHit => grind

def h0 := {{{
  handler {return x ↦ return x, ops := ["op" (x,k) ↦ return x]}
}}}

def hitExample :
  {{{ with ~h0 handle op(True; fun y => (return y)) }}} ⤳ {{{ return True }}} := by
  have := Step.handleOpHit h0 "op" (.bool true) (.ret (.var (.bvar 0)))
    (.ret (.var (.bvar 1))) rfl
  simp [instantiateOpClauseBody, instantiateComputationLvl,
    instantiateValueLvl] at this
  exact this
