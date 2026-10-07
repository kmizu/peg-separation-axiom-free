import Mathlib.Computability.ContextFreeGrammar
import PegSeparation.Closure.GreibachProofCFL
import PegSeparation.Closure.GreibachProofGNFBase

/-!
# From the character grammars to mathlib's grammars

The copied development (`GreibachProof*`) works with grammars `CFGrammar` over `Char` whose semantics is the
tree-shaped `Gen`. This file

- fixes Greibach's seven letters as a finite type `Letter` (`(`, `)`, `[`, `]`, `c`, `¢`, `d`), with
  `Letter.toChar` and its partial inverse `Letter.ofChar`;
- turns a character grammar `G` into a mathlib grammar `toMathlib G` over `Letter`, whose language is
  `{v | G.language (v.map toChar)}` (`toMathlib_language`): right sides with a character outside the seven
  letters are dropped, since terminals are never erased;
- concludes that Greibach's hardest language over `Letter` is context-free in mathlib's sense
  (`hardLanguage_isContextFree`).
-/

namespace PegSeparation.Closure.GreibachProof

/-- **Greibach's seven letters**: the brackets `(`,`)`,`[`,`]`, the letters `c` and `¢`, and the separator `d`. -/
inductive Letter
  | lp | rp | lb | rb | c | cent | d
  deriving DecidableEq, Fintype

namespace Letter

/-- The character of a letter (`¢` is `$`, as in `L0`). -/
def toChar : Letter → Char
  | lp => '('
  | rp => ')'
  | lb => '['
  | rb => ']'
  | c => 'c'
  | cent => '$'
  | d => 'd'

/-- The letter of a character, if it is one of the seven. -/
def ofChar (x : Char) : Option Letter :=
  if x = '(' then some lp else if x = ')' then some rp else if x = '[' then some lb
  else if x = ']' then some rb else if x = 'c' then some c else if x = '$' then some cent
  else if x = 'd' then some d else none

/-- `ofChar` inverts `toChar`. -/
@[simp] theorem ofChar_toChar (l : Letter) : ofChar l.toChar = some l := by
  cases l <;> decide

/-- `ofChar` only returns the letter of the character. -/
theorem toChar_of_ofChar {x : Char} {l : Letter} (h : ofChar x = some l) : l.toChar = x := by
  unfold ofChar at h
  split_ifs at h <;> (cases h; subst_vars; rfl)

/-- `toChar` is injective. -/
theorem toChar_injective : Function.Injective toChar := by
  intro a b h
  have := ofChar_toChar a
  rw [h, ofChar_toChar] at this
  exact (Option.some.inj this).symm

end Letter

open Letter

/-! ## Translating right sides -/

/-- A mathlib right side read back as a character right side. -/
def backSym : Symbol Letter Nat → Sym
  | .terminal l => .t l.toChar
  | .nonterminal j => .nt j

/-- A character symbol as a mathlib symbol, if its terminal is one of the seven letters. -/
def convSym : Sym → Option (Symbol Letter Nat)
  | .t x => (ofChar x).map Symbol.terminal
  | .nt j => some (.nonterminal j)

/-- `convSym` inverts `backSym`. -/
theorem convSym_eq_some_iff {s : Sym} {o : Symbol Letter Nat} : convSym s = some o ↔ backSym o = s := by
  cases s with
  | t x =>
    cases o with
    | terminal l =>
      simp only [convSym, backSym, Option.map_eq_some_iff, Symbol.terminal.injEq, exists_eq_right,
        Sym.t.injEq]
      exact ⟨toChar_of_ofChar, fun h => h ▸ ofChar_toChar l⟩
    | nonterminal j => simp [convSym, backSym]
  | nt i => cases o <;> simp [convSym, backSym, eq_comm]

/-- A character right side as a mathlib right side, if all its terminals are letters. -/
def convRhs (rhs : List Sym) : Option (List (Symbol Letter Nat)) := rhs.mapM convSym

/-- `convRhs` inverts reading back. -/
theorem convRhs_eq_some_iff : ∀ {rhs : List Sym} {out : List (Symbol Letter Nat)},
    convRhs rhs = some out ↔ out.map backSym = rhs
  | [], out => by cases out <;> simp [convRhs]
  | s :: rhs, out => by
    have ih := @convRhs_eq_some_iff rhs
    simp only [convRhs, List.mapM_cons, bind_pure_comp] at ih ⊢
    cases out with
    | nil =>
      simp only [List.map_nil, reduceCtorEq, iff_false]
      intro h
      cases hs : convSym s <;> cases hr : rhs.mapM convSym <;> simp_all
    | cons o out =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · intro h
        cases hs : convSym s with
        | none => simp [hs] at h
        | some o' =>
          cases hr : rhs.mapM convSym with
          | none => simp [hs, hr] at h
          | some out' =>
            simp only [hs, hr] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨convSym_eq_some_iff.mp hs, (ih).mp hr⟩
      · rintro ⟨h1, h2⟩
        rw [convSym_eq_some_iff.mpr h1, (ih).mpr h2]
        rfl

/-! ## The mathlib grammar -/

/-- The mathlib rules of a character grammar, as a list. -/
def ruleList (G : CFGrammar) : List (ContextFreeRule Letter Nat) :=
  (List.range G.rules.length).flatMap fun i =>
    match altsAt G.rules i with
    | none => []
    | some alts => alts.filterMap fun rhs => (convRhs rhs).map fun out => ⟨i, out⟩

/-- Membership in the mathlib rules: the read-back right side is an alternative of the input. -/
theorem mem_ruleList {G : CFGrammar} {r : ContextFreeRule Letter Nat} :
    r ∈ ruleList G ↔ ∃ alts, altsAt G.rules r.input = some alts ∧ r.output.map backSym ∈ alts := by
  simp only [ruleList, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, _, hi⟩
    cases ha : altsAt G.rules i with
    | none => simp [ha] at hi
    | some alts =>
      simp only [ha, List.mem_filterMap, Option.map_eq_some_iff] at hi
      obtain ⟨rhs, hrhs, out, hout, rfl⟩ := hi
      exact ⟨alts, ha, by rw [convRhs_eq_some_iff.mp hout]; exact hrhs⟩
  · rintro ⟨alts, ha, hm⟩
    refine ⟨r.input, altsAt_some_lt ha, ?_⟩
    simp only [ha, List.mem_filterMap, Option.map_eq_some_iff]
    exact ⟨_, hm, r.output, convRhs_eq_some_iff.mpr rfl, rfl⟩

/-- **The mathlib grammar** over the seven letters of a character grammar. -/
abbrev toMathlib (G : CFGrammar) : ContextFreeGrammar Letter where
  NT := Nat
  initial := G.start
  rules := (ruleList G).toFinset

/-! ## Generation gives derivations -/

/-- A right side yielding a letter word reads back from a mathlib right side deriving that word. -/
theorem derives_of_semRhs (G : CFGrammar) (S : Nat → List Char → Prop)
    (hS : ∀ j x, S j x → ∀ v : List Letter, x = v.map toChar →
      (toMathlib G).Derives [.nonterminal j] (v.map .terminal)) :
    ∀ (rhs : List Sym) (x : List Char), SemRhs S rhs x → ∀ v : List Letter, x = v.map toChar →
      ∃ out : List (Symbol Letter Nat), out.map backSym = rhs ∧ (toMathlib G).Derives out (v.map .terminal)
  | [], x, h, v, hv => by
    have hx : x = [] := h
    subst hx
    obtain rfl : v = [] := List.map_eq_nil_iff.mp hv.symm
    exact ⟨[], rfl, .refl _⟩
  | .t ch :: rhs, x, h, v, hv => by
    obtain ⟨x', rfl, h'⟩ := h
    obtain ⟨l, v', rfl, hl, rfl⟩ := List.map_eq_cons_iff.mp hv.symm
    obtain ⟨out, hout, hd⟩ := derives_of_semRhs G S hS rhs _ h' v' rfl
    refine ⟨.terminal l :: out, by simp [backSym, hout, hl], ?_⟩
    simpa using hd.append_left [.terminal l]
  | .nt j :: rhs, x, h, v, hv => by
    obtain ⟨x1, x2, rfl, h1, h2⟩ := h
    obtain ⟨v1, v2, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp hv.symm
    obtain ⟨out, hout, hd⟩ := derives_of_semRhs G S hS rhs _ h2 v2 rfl
    refine ⟨.nonterminal j :: out, by simp [backSym, hout], ?_⟩
    have h1' := (hS j _ h1 v1 rfl).append_right out
    have h2' := hd.append_left (v1.map Symbol.terminal)
    simpa using h1'.trans h2'

/-- **Generation gives a mathlib derivation** of every letter word. -/
theorem derives_of_gen (G : CFGrammar) {i : Nat} {x : List Char} (h : Gen G i x) :
    ∀ v : List Letter, x = v.map toChar → (toMathlib G).Derives [.nonterminal i] (v.map .terminal) := by
  refine gen_sound (fun j x => ∀ v : List Letter, x = v.map toChar →
    (toMathlib G).Derives [.nonterminal j] (v.map .terminal)) ?_ h
  intro j alts rhs x ha hm hsem v hv
  obtain ⟨out, hout, hd⟩ := derives_of_semRhs G _ (fun _ _ h => h) rhs x hsem v hv
  have hr : (⟨j, out⟩ : ContextFreeRule Letter Nat) ∈ (toMathlib G).rules := by
    show _ ∈ (ruleList G).toFinset
    rw [List.mem_toFinset, mem_ruleList]
    exact ⟨alts, ha, by rw [hout]; exact hm⟩
  exact Relation.ReflTransGen.head ⟨_, hr, ContextFreeRule.Rewrites.input_output⟩ hd

/-! ## Derivations give generation -/

/-- A letter word reads back to a right side yielding its characters. -/
theorem semRhs_map_terminal (G : CFGrammar) :
    ∀ v : List Letter, SemRhs (Gen G) ((v.map Symbol.terminal).map backSym) (v.map toChar)
  | [] => rfl
  | _ :: v => ⟨_, rfl, semRhs_map_terminal G v⟩

/-- **A mathlib derivation of a letter word gives generation** from the read-back sentential form. -/
theorem semRhs_of_derives (G : CFGrammar) (v : List Letter) {u : List (Symbol Letter Nat)}
    (h : (toMathlib G).Derives u (v.map .terminal)) : SemRhs (Gen G) (u.map backSym) (v.map toChar) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact semRhs_map_terminal G v
  | head hp _ ih =>
    obtain ⟨r, hr, hrw⟩ := hp
    obtain ⟨p, q, rfl, rfl⟩ := hrw.exists_parts
    have hr' : r ∈ ruleList G := List.mem_toFinset.mp hr
    obtain ⟨alts, ha, hm⟩ := mem_ruleList.mp hr'
    simp only [List.map_append] at ih ⊢
    obtain ⟨y, z, hyz, hy, hz⟩ := (semRhs_append _ _ _ _).mp ih
    obtain ⟨y1, y2, rfl, hy1, hy2⟩ := (semRhs_append _ _ _ _).mp hy
    refine (semRhs_append _ _ _ _).mpr ⟨y1 ++ y2, z, hyz, (semRhs_append _ _ _ _).mpr
      ⟨y1, y2, rfl, hy1, ?_⟩, hz⟩
    simp only [List.map_cons, List.map_nil, backSym]
    exact (semRhs_single_nt _ _ _).mpr (gen_of_rule ha hm hy2)

/-- **The language of the mathlib grammar**: the letter words whose characters the grammar generates. -/
theorem toMathlib_language (G : CFGrammar) (v : List Letter) :
    v ∈ (toMathlib G).language ↔ G.language (v.map toChar) := by
  rw [ContextFreeGrammar.mem_language_iff]
  constructor
  · intro h
    have := semRhs_of_derives G v h
    exact (semRhs_single_nt _ _ _).mp this
  · intro h
    exact derives_of_gen G h v rfl

/-! ## Greibach's hardest language over the seven letters -/

/-- **Greibach's hardest language** over `Letter`: the letter words whose characters are in `L0`. -/
def hardLanguage : Language Letter := {v | L0 (v.map toChar)}

/-- **`hardLanguage` is context-free** in mathlib's sense. -/
theorem hardLanguage_isContextFree : hardLanguage.IsContextFree := by
  refine ⟨toMathlib l0Grammar, ?_⟩
  ext v
  rw [toMathlib_language]
  exact (l0Grammar_language _).symm

end PegSeparation.Closure.GreibachProof
