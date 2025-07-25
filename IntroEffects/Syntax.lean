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

/-
  Improve the formatting of the output
-/
mutual
def Value.format (prec : Nat) : Value → Format
| .var (.bvar n) => .group <| "bvar " ++ reprPrec n 0
| .var (.fvar n) => n
| .bool true => "True"
| .bool false => "False"
| .string s => s
| .unit => "()"
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
| .join v₁ v₂ => .group <| v₁.format prec ++ " ++ " ++ v₂.format prec

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
scoped syntax:arg embedded:arg embedded:max : embedded
/-- A function -/
scoped syntax:max "fun" ident " ↦ " embedded:arg : embedded
/-- Bool true -/
scoped syntax "True" : embedded
/-- Bool false -/
scoped syntax "False" : embedded
/-- Return -/
scoped syntax "return " embedded : embedded
/-- OpCall -/
scoped syntax ident "(" embedded "; " embedded ")" : embedded
/-- Bind -/
scoped syntax "do " ident " ← " embedded " in " embedded : embedded
/-- If then else -/
scoped syntax "if " embedded " then " embedded " else " embedded : embedded
/-- Handler -/
scoped syntax "with " embedded " handle " embedded : embedded
/-- OpClause -/
scoped syntax str "(x,k)" " ↦ " embedded : embedded
scoped syntax "handler " "{" "return " ident " ↦ " embedded ", " "ops " " := " "[" embedded,* "]" "}" : embedded
scoped syntax "handler " "{" "ops " " := " "[" embedded,* "]" "}" : embedded
scoped syntax "str( " str  ")" : embedded
scoped syntax "join(" embedded ", " embedded ")" : embedded
scoped syntax "()" : embedded
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
  `(Computation.handle $hTerm $cTerm)
| `(embedded| ~$e) => pure e
| `(embedded| $t:str (x,k) ↦ $e) => do
  let eTerm ← withBoundIdentifier `x (withBoundIdentifier `k (toTermSyntax e))
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
| `(embedded| str($s:str)) => `(Value.string $s)
| `(embedded| join($e1, $e2)) => do
  let e1Term ← toTermSyntax e1
  let e2Term ← toTermSyntax e2
  `(Computation.join $e1Term $e2Term)
| `(embedded| ()) => `(Value.unit)
| _ => pure <| TSyntax.mk Syntax.missing

@[term_elab embeddedTerm] def elabEmbedded : TermElab := fun stx _ => do
  let body := stx[1]
  let termStx ← (toTermSyntax body).run ⟨[]⟩
  elabTerm termStx.1 none
end Input
