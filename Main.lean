import IntroEffects

-- Examples
open Input

def alwaysRead := {{{
  fun s ↦ (return handler {ops := ["read"(x,k) ↦ k s]})
}}}

def main : IO Unit :=
  IO.println s!"Hello, !"
