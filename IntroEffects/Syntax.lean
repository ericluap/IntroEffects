import IntroEffects.Expr
import Lean

/-!
  Allow for creating terms in the language using nice syntax
  and improve the formatting when displaying terms in the language.
-/

/-
  Make the representations of terms nicer.
-/
section Output
open Std (Format)
open Lean.Parser (maxPrec minPrec argPrec)

/--
  Track the names of the bvars
-/
structure Ctx where
  bound : List String

def Ctx.addBvar (ctx : Ctx) (name : String) : Ctx := ⟨name :: ctx.bound⟩

def Ctx.lookup (ctx : Ctx) (bvar : Nat) : String :=
  ctx.bound[bvar]?.getD (toString bvar)

def Ctx.getNewName (ctx : Ctx) : String := "x" ++ toString ctx.bound.length

/-
  Improve the formatting of the output
-/
mutual
def Value.format (prec : Nat) (ctx : Ctx): Value → Format
| .var (.bvar n) => .group <| ctx.lookup n
| .var (.fvar n) => n
| .bool true => "True"
| .bool false => "False"
| .string s => "\"" ++ s ++ "\""
| .pair v₁ v₂ => .group <| "(" ++  v₁.format prec ctx ++ ", " ++ v₂.format prec ctx ++ ")"
| .unit => "()"
| .lam c =>
  let name := ctx.getNewName
  .group <| "fun " ++ name ++ " ↦ " ++ .nest 2 (.line ++ c.format prec (ctx.addBvar name))
| .hdl h => h.format prec ctx

def Computation.format (prec : Nat) (ctx : Ctx) : Computation → Format
| .ret v => .group <| "return " ++ v.format prec ctx
| .handle h c => .group <| "with " ++ h.format prec ctx ++ " handle" ++ .line ++ .nest 2 (c.format prec ctx)
| .app v₁ v₂ => .group <| v₁.format prec ctx ++ " " ++ v₂.format prec ctx
| .ite v c₁ c₂ => .group <| "if " ++ v.format prec ctx ++ .line ++ " then " ++
  c₁.format prec ctx ++ .line ++ " else " ++ c₂.format prec ctx
| .bind c₁ c₂ =>
  let name := ctx.getNewName
  .group <| "do " ++ name ++ " ← " ++ c₁.format prec ctx ++ " in " ++ .line ++ c₂.format prec (ctx.addBvar name)
| .opCall name v c =>
  let newName := ctx.getNewName
  .group <| name ++ "(" ++ v.format prec ctx ++ "; fun " ++ newName ++ " ↦ " ++ c.format prec (ctx.addBvar newName) ++ ")"
| .join v₁ v₂ => .group <| v₁.format prec ctx ++ " ++ " ++ v₂.format prec ctx
| .fst v => .group <| "fst " ++ v.format prec ctx
| .snd v => .group <| "snd " ++ v.format prec ctx

def OpClause.format (prec : Nat) (ctx : Ctx) : OpClause → Format
| ⟨op, body⟩ =>
  let name1 := ctx.getNewName
  let name2 := (ctx.addBvar name1).getNewName
  let opsCtx := (ctx.addBvar name1).addBvar name2
  .group <| "{" ++ op ++ "(" ++ name1 ++ ", " ++ name2 ++ ") ↦ " ++ .line ++ body.format prec opsCtx ++ "}"
def Handler.format (prec : Nat) (ctx : Ctx) : Handler → Format
| ⟨ret?, ops⟩ =>
  let name := ctx.getNewName
  let retStr := match ret? with
  | none => "none"
  | some ret => "return " ++ name ++ " ↦ " ++ ret.format prec (ctx.addBvar name)
  .group <| "{" ++ retStr ++ ", " ++ .line ++ "ops := [" ++
    .joinSep (ops.map (·.format prec ctx)) (", " ++ .line) ++ "]}"
where
  repr : Option Computation → Format
  | none => "none"
  | some c => c.format prec (ctx.addBvar ctx.getNewName)
end

instance : Repr Computation where
  reprPrec comp n := comp.format n ⟨[]⟩
instance : Repr Value where
  reprPrec value n := value.format n ⟨[]⟩

instance : ToString Computation where
  toString := toString ∘ repr
instance : ToString Value where
  toString := toString ∘ repr
end Output

/-
  Make inputing the terms nicer
-/
namespace Input
open Lean Elab Term Meta

declare_syntax_cat embedded

/-- Variable reference -/
scoped syntax:max ident : embedded
/-- Grouping of expressions -/
scoped syntax "(" embedded ")" : embedded
/-- Application -/
scoped syntax embedded embedded : embedded
/-- A function -/
scoped syntax:max "fun" ident " ↦ " embedded : embedded
/-- Bool true -/
scoped syntax "True" : embedded
/-- Bool false -/
scoped syntax "False" : embedded
/-- Return -/
scoped syntax "return " embedded : embedded
/-- OpCall -/
scoped syntax ident "⟨" embedded "; " embedded "⟩" : embedded
scoped syntax ident "⟨" embedded "⟩" : embedded
/-- Bind -/
scoped syntax "do " ident " ← " embedded " in " embedded : embedded
scoped syntax "do " "(" ident ", " ident ")" " ← " embedded " in " embedded : embedded
scoped syntax "← " embedded ";" embedded : embedded
/-- If then else -/
scoped syntax "if " embedded " then " embedded " else " embedded : embedded
/-- Handler -/
scoped syntax "with " embedded " handle " embedded : embedded
/-- OpClause -/
scoped syntax str "(" ident ", " ident ")" " ↦ " embedded : embedded
scoped syntax "handler " "{" "return " ident " ↦ " embedded ", " "ops " " := " "[" embedded,* "]" "}" : embedded
scoped syntax "handler " "{" "ops " " := " "[" embedded,* "]" "}" : embedded
/-- String -/
scoped syntax "str " str : embedded
/-- Join -/
scoped syntax "join(" embedded ", " embedded ")" : embedded
/-- Unit -/
scoped syntax "()" : embedded
/-- Pair -/
scoped syntax "pair(" embedded ", " embedded ")" : embedded
scoped syntax "fst " embedded : embedded
scoped syntax "snd " embedded : embedded
/-- Embed Lean term -/
scoped syntax:max "~" term:max : embedded
scoped syntax (name := embeddedTerm) "{{{" embedded "}}}" : term

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
| `(embedded| fun $x:ident ↦ $body) => do
  let bodyTerm ← withBoundIdentifier x.getId (toTermSyntax body)
  `(Value.lam $bodyTerm)
| `(embedded| $f $arg) => do
  let fTerm ← toTermSyntax f
  let argTerm ← toTermSyntax arg
  `(Computation.app $fTerm $argTerm)
| `(embedded| return $e) => do
  let t ← toTermSyntax e
  `(Computation.ret $t)
| `(embedded| $op:ident ⟨ $v ; $k ⟩) => do
  let vTerm ← toTermSyntax v
  /-
    Extract the body of the lambda because
    `opCall` expects a computation with one dangling bvar
  -/
  let kTerm := extractLambdaBody (←toTermSyntax k)
  `(Computation.opCall $(Lean.quote op.getId.toString) $vTerm $kTerm)
-- Default return in op call
| `(embedded| $op:ident ⟨$v⟩) => do
  let newSyntax : TSyntax `embedded ← `(embedded| $op:ident ⟨$v; fun y ↦ (return y)⟩)
  toTermSyntax newSyntax.raw
| `(embedded| do $x:ident ← $c₁ in $c₂) => do
  let c₁Term ← toTermSyntax c₁
  let c₂Term ← withBoundIdentifier x.getId (toTermSyntax c₂)
  `(Computation.bind $c₁Term $c₂Term)
| `(embedded| ← $c₁; $c₂) => do
  let c₁Term ← toTermSyntax c₁
  let c₂Term ← withBoundIdentifier (←mkFreshUserName `x) (toTermSyntax c₂)
  `(Computation.bind $c₁Term $c₂Term)
| `(embedded| if $v then $c₁ else $c₂) => do
  let vTerm ← toTermSyntax v
  let c₁Term ← toTermSyntax c₁
  let c₂Term ← toTermSyntax c₂
  `(Computation.ite $vTerm $c₁Term $c₂Term)
| `(embedded| with $h handle $c) => do
  let hTerm ← toTermSyntax h
  let cTerm ← toTermSyntax c
  `(Computation.handle $hTerm $cTerm)
| `(embedded| ~$e) => pure e
| `(embedded| $t:str ($x, $k) ↦ $e) => do
  let eTerm ← withBoundIdentifier x.getId (withBoundIdentifier k.getId (toTermSyntax e))
  `(OpClause.mk $t $eTerm)
| `(embedded| handler {return $x ↦ $e, ops := [$xs,*] }) => do
  -- Assumed to have one dangling bvar
  let eTerm ← withBoundIdentifier x.getId (toTermSyntax e)
  -- Each is assumed to have two dangling bvars
  let opsTerms ← xs.getElems.mapM (toTermSyntax ·)
  `(Value.hdl (Handler.mk (some $eTerm) [$opsTerms,*]))
| `(embedded| handler {ops := [$xs,*] }) => do
    let opsTerms ← xs.getElems.mapM (toTermSyntax ·)
    `(Value.hdl (Handler.mk none [$opsTerms,*]))
-- str
| `(embedded| str $s:str) => `(Value.string $s)
-- join
| `(embedded| join($e1, $e2)) => do
  let e1Term ← toTermSyntax e1
  let e2Term ← toTermSyntax e2
  `(Computation.join $e1Term $e2Term)
-- Unit
| `(embedded| ()) => `(Value.unit)
-- Pair construction
| `(embedded| pair($e1, $e2)) => do
  let e1Term ← toTermSyntax e1
  let e2Term ← toTermSyntax e2
  `(Value.pair $e1Term $e2Term)
-- fst
| `(embedded| fst $e) => do
  let eTerm ← toTermSyntax e
  `(Computation.fst $eTerm)
-- snd
| `(embedded| snd $e) => do
  let eTerm ← toTermSyntax e
  `(Computation.snd $eTerm)
-- Bind pair destruction
| `(embedded| do ($x, $y) ← $c₁ in $c₂) => do
  let newSyntax : TSyntax `embedded ← `(embedded|
    do c ← $c₁ in
    do $x ← fst c in
    do $y ← snd c in
    $c₂)
  toTermSyntax newSyntax.raw
| _ => pure <| TSyntax.mk Syntax.missing

@[term_elab embeddedTerm] def elabEmbedded : TermElab := fun stx _ => do
  let body := stx[1]
  let termStx ← (toTermSyntax body).run ⟨[]⟩
  elabTerm termStx.1 none
end Input
