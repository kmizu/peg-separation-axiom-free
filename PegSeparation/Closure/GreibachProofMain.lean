import PegSeparation.Closure.GreibachHardest
import PegSeparation.Closure.GreibachProofStd
import PegSeparation.Closure.GreibachProofGNF
import PegSeparation.Closure.GreibachProofToMathlib
import PegSeparation.Closure.GreibachProofOfMathlib

/-!
# Greibach's hardest context-free language, proved

This file discharges `PegSeparation.External.Greibach1973.hardestContextFreeLanguage` by building
`greibachWitness : PegSeparation.Closure.GreibachHardest.Witness` from the copied character-grammar
development (after Nipkow's AFP `Greibach_Hardest`):

1. the hard language is `hardLanguage` over the seven letters `Letter`, context-free in mathlib's sense
   (`hardLanguage_isContextFree`, from `l0_cfl`);
2. a mathlib grammar `g` over a finite alphabet `Source` becomes the character grammar `ofMathlib g enc`,
   where `enc` encodes the `k`-th letter by the unary prefix code `0ᵏ1`, so that `encW enc` is injective;
3. `stdForm_exists` puts that grammar into Greibach's standard form, and `greibach_std` gives the
   nonerasing homomorphism `encH` with `L - {ε} = encH⁻¹(L0 - {ε})`;
4. the composite `a ↦ encH(enc a)`, read in `Letter`, is the reduction; `ε` decides between
   `h⁻¹(hardLanguage)` and `h⁻¹(hardLanguage - 1)`.
-/

namespace PegSeparation.Closure.GreibachProof

open Letter GStd

/-! ## The unary prefix code -/

/-- The unary code `0ᵏ1`. -/
def ucode (k : Nat) : List Char := List.replicate k '0' ++ ['1']

/-- The unary code is a prefix code. -/
theorem ucode_append_inj : ∀ {i j : Nat} {s t : List Char}, ucode i ++ s = ucode j ++ t → i = j ∧ s = t
  | 0, 0, s, t, h => ⟨rfl, by simpa [ucode] using h⟩
  | 0, j + 1, s, t, h => by simp [ucode, List.replicate_succ] at h
  | i + 1, 0, s, t, h => by simp [ucode, List.replicate_succ] at h
  | i + 1, j + 1, s, t, h => by
    simp only [ucode, List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := ucode_append_inj (i := i) (j := j) h
    exact ⟨rfl, rfl⟩

/-- The unary code is never empty. -/
theorem ucode_ne_nil (k : Nat) : ucode k ≠ [] := by simp [ucode]

/-- Encoding words letter by letter with an injective letter numbering is injective. -/
theorem encW_ucode_injective {T : Type} {e : T → Nat} (he : Function.Injective e) :
    ∀ {w w' : List T}, encW (fun a => ucode (e a)) w = encW (fun a => ucode (e a)) w' → w = w'
  | [], [], _ => rfl
  | [], a :: w', h => by
    have : ucode (e a) ++ encW (fun a => ucode (e a)) w' = [] := by simpa [encW] using h.symm
    exact absurd (List.append_eq_nil_iff.mp this).1 (ucode_ne_nil _)
  | a :: w, [], h => by
    have : ucode (e a) ++ encW (fun a => ucode (e a)) w = [] := by simpa [encW] using h
    exact absurd (List.append_eq_nil_iff.mp this).1 (ucode_ne_nil _)
  | a :: w, a' :: w', h => by
    have h' : ucode (e a) ++ encW (fun a => ucode (e a)) w = ucode (e a') ++ encW (fun a => ucode (e a)) w' := by
      simpa [encW] using h
    obtain ⟨hi, hr⟩ := ucode_append_inj h'
    rw [he hi, encW_ucode_injective he hr]

/-- A nonempty word has a nonempty unary encoding. -/
theorem encW_ucode_ne_nil {T : Type} (e : T → Nat) {w : List T} (hw : w ≠ []) :
    encW (fun a => ucode (e a)) w ≠ [] := by
  cases w with
  | nil => exact absurd rfl hw
  | cons a w => simp [encW, ucode]

/-! ## The letters of Greibach's homomorphism -/

/-- `¢` and the brackets are letters. -/
theorem ofChar_isSome_of_chars {x : Char} (h : x = '$' ∨ isBracket x = true) : (ofChar x).isSome := by
  rcases h with rfl | h
  · decide
  · simp only [isBracket, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ((rfl | rfl) | rfl) | rfl <;> decide

/-- **Every character of `encH` is one of the seven letters.** -/
theorem encH_letters (S : Nat) (P : List GProd) (a : Char) : ∀ x ∈ encH S P a, (ofChar x).isSome := by
  intro x hx
  simp only [encH, List.mem_append, List.mem_flatten, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with ⟨_, ⟨p, _, rfl⟩, hx⟩ | rfl | rfl
  · rcases List.mem_cons.mp hx with rfl | hx
    · decide
    · exact ofChar_isSome_of_chars (xihat_chars S p x hx)
  · decide
  · decide

/-- **Greibach's theorem for standard form, with the homomorphism named** (`greibach_std` with `h = encH`). -/
theorem greibach_std_encH (G : CFGrammar) (hs : StdForm G) :
    (∀ a, encH G.start (prods G) a ≠ []) ∧
      ∀ w, w ≠ [] → (G.language w ↔ invHom (encH G.start (prods G)) L0 w) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨p, hp, _⟩ := encH_d G.start (prods G) a
    rw [hp] at ha
    simp at ha
  · intro w hw
    rw [language_iff_drives hs]
    constructor
    · rintro ⟨ps, hd⟩
      exact forward hs hd
    · intro hL
      exact backward G hw hL

/-! ## Reading character words as letter words -/

/-- Reading the letters of a character word whose characters are all letters loses nothing. -/
theorem map_toChar_filterMap_ofChar :
    ∀ (xs : List Char), (∀ x ∈ xs, (ofChar x).isSome) → (xs.filterMap ofChar).map toChar = xs
  | [], _ => rfl
  | x :: xs, h => by
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (h x List.mem_cons_self)
    rw [List.filterMap_cons_some hl, List.map_cons, toChar_of_ofChar hl,
      map_toChar_filterMap_ofChar xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- The letter image of a character word under a homomorphism whose images are letters. -/
def letterWord (H : Char → List Char) (cs : List Char) : List Letter :=
  cs.flatMap fun ch => (H ch).filterMap ofChar

/-- Reading back the letter image gives the character image. -/
theorem map_toChar_letterWord {H : Char → List Char} (hH : ∀ ch, ∀ x ∈ H ch, (ofChar x).isSome) :
    ∀ cs : List Char, (letterWord H cs).map toChar = (cs.map H).flatten
  | [] => rfl
  | ch :: cs => by
    show ((H ch).filterMap ofChar ++ letterWord H cs).map toChar = H ch ++ (cs.map H).flatten
    rw [List.map_append, map_toChar_filterMap_ofChar _ (hH ch), map_toChar_letterWord hH cs]

/-- `letterWord` turns concatenation into concatenation. -/
theorem letterWord_append (H : Char → List Char) (cs ds : List Char) :
    letterWord H (cs ++ ds) = letterWord H cs ++ letterWord H ds :=
  List.flatMap_append

/-! ## The reduction -/

/-- The letter homomorphism of the reduction: `a ↦ H(enc a)` read in `Letter`. -/
def reductionHom {Source : Type} (enc : Source → List Char) (H : Char → List Char) : WordHom Source Letter :=
  ⟨fun a => letterWord H (enc a)⟩

/-- The reduction homomorphism extends to `letterWord` of the encoding. -/
theorem reductionHom_extend {Source : Type} (enc : Source → List Char) (H : Char → List Char) :
    ∀ w : List Source, (reductionHom enc H).extend w = letterWord H (encW enc w)
  | [] => rfl
  | a :: w => by
    rw [WordHom.extend_cons, reductionHom_extend enc H w]
    simp only [encW, List.map_cons, List.flatten_cons, letterWord_append]
    rfl

/-- The reduction homomorphism is nonerasing when both the code and `H` are. -/
theorem reductionHom_ne_nil {Source : Type} {enc : Source → List Char} {H : Char → List Char}
    (henc : ∀ a, enc a ≠ []) (hH : ∀ ch, H ch ≠ []) (hH' : ∀ ch, ∀ x ∈ H ch, (ofChar x).isSome) (a : Source) :
    (reductionHom enc H).letterImage a ≠ [] := by
  intro he
  have h1 : (letterWord H (enc a)).map toChar = ((enc a).map H).flatten := map_toChar_letterWord hH' _
  change letterWord H (enc a) = [] at he
  rw [he, List.map_nil] at h1
  obtain ⟨ch, cs, hcs⟩ := List.exists_cons_of_ne_nil (henc a)
  rw [hcs, List.map_cons, List.flatten_cons] at h1
  exact hH ch (List.append_eq_nil_iff.mp h1.symm).1

/-- The empty word is in Greibach's hardest language. -/
theorem nil_mem_hardLanguage : ([] : List Letter) ∈ hardLanguage := Or.inl rfl

/-- **The reduction, nonerasing**: every context-free language over a finite alphabet is the inverse image of
`hardLanguage`, or of `hardLanguage - 1`, under a nonerasing homomorphism. -/
theorem reduction_nonerasing (Source : Type) [Fintype Source] (L : Language Source) (hL : L.IsContextFree) :
    ∃ hom : WordHom Source Letter, (∀ a, hom.letterImage a ≠ []) ∧
      (L = hom.inverseImage hardLanguage ∨ L = hom.inverseImage (hardLanguage - 1)) := by
  obtain ⟨g, rfl⟩ := hL
  let e : Source → Nat := fun a => (Fintype.equivFin Source a : Nat)
  have he : Function.Injective e := fun a b h => (Fintype.equivFin Source).injective (Fin.ext h)
  let enc : Source → List Char := fun a => ucode (e a)
  let G := ofMathlib g enc
  let G' := greibachG G
  let H := encH G'.start (prods G')
  obtain ⟨hHne, hstd⟩ := greibach_std_encH G' (greibachG_stdForm G)
  have hH' : ∀ ch, ∀ x ∈ H ch, (ofChar x).isSome := encH_letters _ _
  let hom := reductionHom enc H
  -- the nonempty words
  have key : ∀ w : List Source, w ≠ [] → (w ∈ g.language ↔ hom.extend w ∈ hardLanguage) := by
    intro w hw
    have hne : encW enc w ≠ [] := encW_ucode_ne_nil e hw
    have h1 : w ∈ g.language ↔ G.language (encW enc w) := by
      rw [ofMathlib_language]
      constructor
      · intro h; exact ⟨w, h, rfl⟩
      · rintro ⟨w', hw', hx⟩
        rwa [encW_ucode_injective he hx]
    rw [h1, greibachG_language G _ hne, hstd _ hne]
    show L0 _ ↔ L0 _
    rw [reductionHom_extend, map_toChar_letterWord hH']
  have hextend : ∀ w : List Source, hom.extend w = [] → w = [] := by
    intro w h
    cases w with
    | nil => rfl
    | cons a w =>
      rw [WordHom.extend_cons] at h
      exact absurd (List.append_eq_nil_iff.mp h).1 (reductionHom_ne_nil (fun _ => ucode_ne_nil _) hHne hH' a)
  refine ⟨hom, reductionHom_ne_nil (fun _ => ucode_ne_nil _) hHne hH', ?_⟩
  by_cases hε : [] ∈ g.language
  · left
    ext w
    rw [WordHom.mem_inverseImage_iff]
    by_cases hw : w = []
    · subst hw; exact ⟨fun _ => nil_mem_hardLanguage, fun _ => hε⟩
    · exact key w hw
  · right
    ext w
    rw [WordHom.mem_inverseImage_iff]
    show _ ↔ _ ∈ hardLanguage ∧ _ ∉ (1 : Language Letter)
    rw [Language.mem_one]
    by_cases hw : w = []
    · subst hw; exact ⟨fun h => absurd h hε, fun h => absurd rfl h.2⟩
    · rw [← key w hw]
      exact ⟨fun h => ⟨h, fun h' => hw (hextend w h')⟩, fun h => h.1⟩

end PegSeparation.Closure.GreibachProof

namespace PegSeparation.Closure.GreibachProof

open PegSeparation.Closure.GreibachHardest

/-- **Greibach's hardest context-free language** (Greibach 1973), as a witness for the artifact's
`GreibachHardest.Witness`: the language `hardLanguage` over the seven letters `Letter`. -/
noncomputable def greibachWitness : PegSeparation.Closure.GreibachHardest.Witness where
  HardAlphabet := Letter
  hardAlphabetFintype := inferInstance
  hardAlphabetDecidableEq := inferInstance
  language := hardLanguage
  isContextFree := hardLanguage_isContextFree
  reduction := fun Source _ _ L hL =>
    (reduction_nonerasing Source L hL).imp fun _ h => h.2

/-- **The reduction homomorphisms are nonerasing.** -/
theorem greibachWitness_nonerasing :
    ∀ (Source : Type) (_ : Fintype Source) (_ : DecidableEq Source) (L : Language Source), L.IsContextFree →
      ∃ hom : PegSeparation.Closure.WordHom Source greibachWitness.HardAlphabet, (∀ a, hom.letterImage a ≠ []) ∧
        (L = hom.inverseImage greibachWitness.language ∨ L = hom.inverseImage (greibachWitness.language - 1)) :=
  fun Source _ _ L hL => reduction_nonerasing Source L hL

/-- **Greibach's hardest-language statement holds** — without the artifact's axiom. -/
theorem hardestContextFreeLanguage_proved : PegSeparation.Closure.GreibachHardest.Statement :=
  ⟨greibachWitness⟩

end PegSeparation.Closure.GreibachProof

#print axioms PegSeparation.Closure.GreibachProof.greibachWitness
#print axioms PegSeparation.Closure.GreibachProof.greibachWitness_nonerasing
#print axioms PegSeparation.Closure.GreibachProof.hardestContextFreeLanguage_proved
