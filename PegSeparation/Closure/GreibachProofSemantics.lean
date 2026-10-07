import PegSeparation.Closure.GreibachProofSyntax

/-!
# Character context-free grammar semantics (copied development)

Generation `Gen g i w` is tree-shaped: nonterminal `i` picks one alternative and its symbols generate
consecutive pieces of `w`, left to right. `GreibachProofToMathlib` and `GreibachProofOfMathlib` prove that this
agrees with mathlib's rewriting semantics `ContextFreeGrammar.Derives`.
-/

namespace PegSeparation.Closure.GreibachProof

mutual
  /-- Nonterminal `i` generates string `w`: expand into one alternative
  (`hmem : rhs ∈ alts`), then resolve each symbol of that alternative left to
  right via `GenRhs`. -/
  inductive Gen (g : CFGrammar) : Nat → List Char → Prop where
    | prod (i : Nat) (alts : List Rhs) (rhs : List Sym) (w : List Char)
        (halts : altsAt g.rules i = some alts) (hmem : rhs ∈ alts)
        (hrhs : GenRhs g rhs w) :
        Gen g i w

  inductive GenRhs (g : CFGrammar) : List Sym → List Char → Prop where
    | nil : GenRhs g [] []
    | cons_t (c : Char) (rest : List Sym) (w : List Char)
        (h : GenRhs g rest w) :
        GenRhs g (.t c :: rest) (c :: w)
    | cons_nt (j : Nat) (rest : List Sym) (w₁ w₂ : List Char)
        (h₁ : Gen g j w₁) (h₂ : GenRhs g rest w₂) :
        GenRhs g (.nt j :: rest) (w₁ ++ w₂)
end

abbrev CharLanguage := List Char → Prop

def CFGrammar.language (g : CFGrammar) : CharLanguage := fun w => Gen g g.start w

def IsCFL (L : CharLanguage) : Prop := ∃ g : CFGrammar, ∀ w, L w ↔ g.language w

end PegSeparation.Closure.GreibachProof
