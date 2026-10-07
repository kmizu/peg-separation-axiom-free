import Mathlib.Computability.ContextFreeGrammar
import PegSeparation.Closure.GreibachProofGNFBase

/-!
# From mathlib's grammars to the character grammars

A mathlib grammar `g` over any alphabet `T` becomes a character grammar `ofMathlib g enc` once every letter
`a` is encoded as a character word `enc a`: the nonterminals are numbered by their position in a list of the
start and the left sides, and each right side is translated symbol by symbol (a letter `a` becomes the
terminals of `enc a`). Its language is the image of `g.language` under `enc` (`ofMathlib_language`).

The encoding of letters as words (instead of single characters) lets the alphabet `T` be arbitrarily large.
-/

namespace PegSeparation.Closure.GreibachProof

attribute [local instance] Classical.propDecidable

variable {T : Type} (g : ContextFreeGrammar T) (enc : T → List Char)

/-- The nonterminals that get numbers: the start and the left sides. -/
noncomputable def ntList : List g.NT := (insert g.initial (g.rules.image ContextFreeRule.input)).toList

/-- The number of a nonterminal (its position in `ntList`). -/
noncomputable def ntIdx (n : g.NT) : Nat := (ntList g).idxOf n

/-- A mathlib symbol as character symbols. -/
noncomputable def mlSym : Symbol T g.NT → List Sym
  | .terminal a => (enc a).map Sym.t
  | .nonterminal n => [.nt (ntIdx g n)]

/-- A mathlib sentential form as a character right side. -/
noncomputable def mlStr (u : List (Symbol T g.NT)) : List Sym := u.flatMap (mlSym g enc)

/-- **The character grammar** of a mathlib grammar, with letters encoded by `enc`. -/
noncomputable def ofMathlib : CFGrammar where
  rules := (ntList g).map fun A =>
    (g.rules.toList.filter fun r => r.input = A).map fun r => mlStr g enc r.output
  start := ntIdx g g.initial

/-- The encoding of a word: the concatenated codes of its letters. -/
def encW (w : List T) : List Char := (w.map enc).flatten

/-! ## Basic facts -/

/-- Left sides are numbered. -/
theorem input_mem_ntList {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) : r.input ∈ ntList g := by
  simp only [ntList, Finset.mem_toList, Finset.mem_insert, Finset.mem_image]
  exact Or.inr ⟨r, hr, rfl⟩

/-- The start is numbered. -/
theorem initial_mem_ntList : g.initial ∈ ntList g := by
  simp [ntList]

/-- A numbered nonterminal sits at its number. -/
theorem getElem_ntIdx {n : g.NT} (h : ntIdx g n < (ntList g).length) : (ntList g)[ntIdx g n] = n :=
  List.getElem_idxOf h

/-- The number of a numbered nonterminal is in range. -/
theorem ntIdx_lt {n : g.NT} (h : n ∈ ntList g) : ntIdx g n < (ntList g).length :=
  List.idxOf_lt_length_iff.mpr h

/-- `mlStr` distributes over concatenation. -/
@[simp] theorem mlStr_append (u v : List (Symbol T g.NT)) : mlStr g enc (u ++ v) = mlStr g enc u ++ mlStr g enc v :=
  List.flatMap_append

/-- `mlStr` of a word is the terminals of its encoding. -/
theorem mlStr_map_terminal (w : List T) : mlStr g enc (w.map .terminal) = (encW enc w).map Sym.t := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, encW, List.flatten_cons, List.map_append] at ih ⊢
    rw [← ih]
    rfl

/-- A right side of terminals yields exactly their characters. -/
theorem semRhs_map_t_iff (S : Nat → List Char → Prop) :
    ∀ (cs x : List Char), SemRhs S (cs.map Sym.t) x ↔ x = cs
  | [], x => Iff.rfl
  | ch :: cs, x => by
    simp only [List.map_cons, SemRhs]
    constructor
    · rintro ⟨x', rfl, h⟩
      rw [(semRhs_map_t_iff S cs x').mp h]
    · rintro rfl
      exact ⟨cs, rfl, (semRhs_map_t_iff S cs cs).mpr rfl⟩

/-- The alternatives of a number. -/
theorem altsAt_ofMathlib (i : Nat) :
    altsAt (ofMathlib g enc).rules i = ((ntList g)[i]?).map fun A =>
      (g.rules.toList.filter fun r => r.input = A).map fun r => mlStr g enc r.output := by
  rw [altsAt_eq_getElem?]
  simp [ofMathlib]

/-- The translation of a rule is an alternative of its left side's number. -/
theorem mem_altsAt_ofMathlib {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    ∃ alts, altsAt (ofMathlib g enc).rules (ntIdx g r.input) = some alts ∧ mlStr g enc r.output ∈ alts := by
  have hlt := ntIdx_lt g (input_mem_ntList g hr)
  refine ⟨_, by rw [altsAt_ofMathlib, List.getElem?_eq_getElem hlt, getElem_ntIdx g hlt]; rfl, ?_⟩
  simp only [List.mem_map, List.mem_filter, Finset.mem_toList, decide_eq_true_eq]
  exact ⟨r, ⟨hr, rfl⟩, rfl⟩

/-- An alternative is the translation of a rule of the numbered nonterminal. -/
theorem of_mem_altsAt_ofMathlib {i : Nat} {alts : List Rhs} {rhs : Rhs}
    (ha : altsAt (ofMathlib g enc).rules i = some alts) (hm : rhs ∈ alts) :
    ∃ (hi : i < (ntList g).length), ∃ r ∈ g.rules, r.input = (ntList g)[i] ∧ rhs = mlStr g enc r.output := by
  rw [altsAt_ofMathlib] at ha
  obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hA
  simp only [List.mem_map, List.mem_filter, Finset.mem_toList, decide_eq_true_eq] at hm
  obtain ⟨r, ⟨hr, hin⟩, rfl⟩ := hm
  exact ⟨hi, r, hr, hin, rfl⟩

/-! ## Derivations give generation -/

/-- **A mathlib derivation of a word gives generation of its encoding** from the translated form. -/
theorem semRhs_of_derives_ofMathlib (w : List T) {u : List (Symbol T g.NT)}
    (h : g.Derives u (w.map .terminal)) : SemRhs (Gen (ofMathlib g enc)) (mlStr g enc u) (encW enc w) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rw [mlStr_map_terminal]; exact (semRhs_map_t_iff _ _ _).mpr rfl
  | head hp _ ih =>
    obtain ⟨r, hr, hrw⟩ := hp
    obtain ⟨p, q, rfl, rfl⟩ := hrw.exists_parts
    obtain ⟨alts, ha, hm⟩ := mem_altsAt_ofMathlib g enc hr
    simp only [mlStr_append] at ih ⊢
    obtain ⟨y, z, hyz, hy, hz⟩ := (semRhs_append _ _ _ _).mp ih
    obtain ⟨y1, y2, rfl, hy1, hy2⟩ := (semRhs_append _ _ _ _).mp hy
    refine (semRhs_append _ _ _ _).mpr ⟨y1 ++ y2, z, hyz, (semRhs_append _ _ _ _).mpr
      ⟨y1, y2, rfl, hy1, ?_⟩, hz⟩
    simp only [mlStr, List.flatMap_cons, List.flatMap_nil, List.append_nil, mlSym]
    exact (semRhs_single_nt _ _ _).mpr (gen_of_rule ha hm hy2)

/-! ## Generation gives derivations -/

/-- The interpretation: a number in range whose nonterminal derives a word encoded as the given one. -/
def OfMathlibSem (i : Nat) (x : List Char) : Prop :=
  ∃ (hi : i < (ntList g).length), ∃ w : List T, x = encW enc w ∧
    g.Derives [.nonterminal (ntList g)[i]] (w.map .terminal)

/-- A translated right side yielding a word under the interpretation derives a word encoded as it. -/
theorem derives_of_semRhs_ofMathlib :
    ∀ (out : List (Symbol T g.NT)) (x : List Char), SemRhs (OfMathlibSem g enc) (mlStr g enc out) x →
      ∃ w : List T, x = encW enc w ∧ g.Derives out (w.map .terminal)
  | [], x, h => ⟨[], h, .refl _⟩
  | .terminal a :: out, x, h => by
    rw [show (Symbol.terminal a :: out) = [.terminal a] ++ out from rfl, mlStr_append] at h
    obtain ⟨x1, x2, rfl, h1, h2⟩ := (semRhs_append _ _ _ _).mp h
    have hx1 : x1 = enc a := by
      simpa [mlStr, mlSym] using (semRhs_map_t_iff _ (enc a) x1).mp (by simpa [mlStr, mlSym] using h1)
    obtain ⟨w, rfl, hd⟩ := derives_of_semRhs_ofMathlib out x2 h2
    refine ⟨a :: w, by simp [encW, hx1], ?_⟩
    simpa using hd.append_left [.terminal a]
  | .nonterminal n :: out, x, h => by
    rw [show (Symbol.nonterminal n :: out) = [.nonterminal n] ++ out from rfl, mlStr_append] at h
    obtain ⟨x1, x2, rfl, h1, h2⟩ := (semRhs_append _ _ _ _).mp h
    simp only [mlStr, List.flatMap_cons, List.flatMap_nil, List.append_nil, mlSym] at h1
    obtain ⟨hi, w1, rfl, hd1⟩ := (semRhs_single_nt _ _ _).mp h1
    rw [getElem_ntIdx g hi] at hd1
    obtain ⟨w2, rfl, hd2⟩ := derives_of_semRhs_ofMathlib out x2 h2
    refine ⟨w1 ++ w2, by simp [encW], ?_⟩
    have := (hd1.append_right out).trans (hd2.append_left (w1.map Symbol.terminal))
    simpa using this

/-- **Generation gives a mathlib derivation** of a word encoded as the generated one. -/
theorem ofMathlibSem_of_gen {i : Nat} {x : List Char} (h : Gen (ofMathlib g enc) i x) :
    OfMathlibSem g enc i x := by
  refine gen_sound (OfMathlibSem g enc) ?_ h
  intro j alts rhs x ha hm hsem
  obtain ⟨hj, r, hr, hin, rfl⟩ := of_mem_altsAt_ofMathlib g enc ha hm
  obtain ⟨w, rfl, hd⟩ := derives_of_semRhs_ofMathlib g enc r.output x hsem
  refine ⟨hj, w, rfl, ?_⟩
  rw [← hin]
  exact Relation.ReflTransGen.head ⟨r, hr, ContextFreeRule.Rewrites.input_output⟩ hd

/-! ## The language -/

/-- **The language of the character grammar** is the encoded language of the mathlib grammar. -/
theorem ofMathlib_language (x : List Char) :
    (ofMathlib g enc).language x ↔ ∃ w ∈ g.language, x = encW enc w := by
  constructor
  · intro h
    obtain ⟨hi, w, rfl, hd⟩ := ofMathlibSem_of_gen g enc h
    rw [show (ntList g)[(ofMathlib g enc).start]'hi = g.initial from getElem_ntIdx g hi] at hd
    exact ⟨w, hd, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    have := semRhs_of_derives_ofMathlib g enc w hw
    simp only [mlStr, List.flatMap_cons, List.flatMap_nil, List.append_nil, mlSym] at this
    exact (semRhs_single_nt _ _ _).mp this

end PegSeparation.Closure.GreibachProof
