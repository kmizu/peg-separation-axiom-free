/-!
# Character context-free grammars (copied development)

Copied, with the namespace renamed, from the Lean development `Cfg/` of the `lean4-peg` project (which
follows Nipkow's AFP `Greibach_Hardest`). These grammars are the working representation for the proof of
Greibach's hardest-language theorem; `GreibachProofToMathlib` and `GreibachProofOfMathlib` translate
between them and mathlib's `ContextFreeGrammar`.

- nonterminals are `Nat` indices, terminals are `Char`;
- `CFGrammar.rules : List (List Rhs)` lists the alternatives of nonterminal `i` at position `i`; a
  nonterminal without a slot generates nothing.
-/

namespace PegSeparation.Closure.GreibachProof

/-- One right-hand-side symbol: a terminal character or a nonterminal
index. -/
inductive Sym where
  | t (c : Char)
  | nt (i : Nat)
  deriving DecidableEq

/-- One production's right-hand side; `[]` is the ε-production. General
(unrestricted) shape — GNF-ness is checked separately, below, not baked into
this type, so `CFGrammar` can faithfully state the textbook notion of CFL
before any normalization. -/
abbrev Rhs := List Sym

structure CFGrammar where
  rules : List (List Rhs)
  start : Nat

/-- Monomorphic alternative-list lookup for nonterminal `i` (mirrors
`ruleAt`/`ruleAtM`). -/
def altsAt : List (List Rhs) → Nat → Option (List Rhs)
  | [], _ => none
  | r :: _, 0 => some r
  | _ :: rs, n + 1 => altsAt rs n

/-! ## Greibach Normal Form, as a decidable `Bool` predicate

Not a type-level restriction — see the module docstring. `isGnfB g = true`
is a decidable shape check on grammars. -/

def symIsNt : Sym → Bool
  | .nt _ => true
  | .t _ => false

/-- A single `Rhs` is GNF-shaped: NON-EMPTY, `.t _ :: rest` with every
element of `rest` a nonterminal (no terminal anywhere but the head, no bare
ε — see the module docstring on why ε is disallowed everywhere, not just
outside the start symbol). -/
def rhsIsGnfB : Rhs → Bool
  | [] => false
  | .t _ :: rest => rest.all symIsNt
  | .nt _ :: _ => false

def isGnfB (g : CFGrammar) : Bool :=
  g.rules.all (fun alts => alts.all rhsIsGnfB)

/-- For a GNF-shaped `Rhs`, the nonterminal sequence following the leading
terminal. -/
def ntSeq : Rhs → List Nat
  | [] => []
  | .nt j :: rest => j :: ntSeq rest
  | .t _ :: rest => ntSeq rest -- dead under `isGnfB g = true`

/-- For a GNF-shaped `Rhs`: `some (c, js)` for `.t c :: rest` with `js` the
nonterminal sequence in `rest` — the only reachable case once `isGnfB g =
true` (ε is disallowed entirely; see the module docstring). The `[]`/`.nt _
:: _` arms are dead under that hypothesis (kept for totality, like
`pegRun`'s dead star-fail branch). -/
def gnfHead : Rhs → Option (Char × List Nat)
  | [] => none
  | .t c :: rest => some (c, ntSeq rest)
  | .nt _ :: _ => none

end PegSeparation.Closure.GreibachProof
