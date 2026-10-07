import PegSeparation.CFLNotPEG.Witness.LanguageCFG
import PegSeparation.Common.Model.LinearContextFreeGrammar


namespace PegSeparation.Witness.LanguageCFG

namespace LinearGrammar

open Grammar

inductive NT where
  | A | D | E | R | DPrime | EPrime | K | P0 | P1
  deriving DecidableEq, Fintype, Repr

inductive RuleName where
  | aSkip0 | aSkip1 | aWitness0 | aWitness1
  | dKey0 | dKey1 | dPayload0 | dPayload1
  | ePayload0 | ePayload1 | eEnd
  | rEnd | rRecord0 | rRecord1
  | dPrimeKey0 | dPrimeKey1 | dPrimePayload0 | dPrimePayload1
  | ePrimePayload0 | ePrimePayload1 | ePrimeEnd
  | kWrap0 | kWrap1 | kBase
  | p0Base | p000 | p001 | p010 | p011
  | p100 | p101 | p110 | p111
  deriving DecidableEq, Fintype, Repr

abbrev GSymbol := Symbol Terminal NT
abbrev Sentential := List GSymbol

private def tm (a : Terminal) : GSymbol := .terminal a
private def nt (n : NT) : GSymbol := .nonterminal n

private def rule (input : NT) (output : Sentential) :
    ContextFreeRule Terminal NT :=
  ⟨input, output⟩

def production : RuleName → ContextFreeRule Terminal NT
  | .aSkip0 => rule .A [tm .langle, tm .bit0, nt .D]
  | .aSkip1 => rule .A [tm .langle, tm .bit1, nt .D]
  | .aWitness0 => rule .A [tm .langle, tm .bit0, nt .K, tm .bit0]
  | .aWitness1 => rule .A [tm .langle, tm .bit1, nt .K, tm .bit1]
  | .dKey0 => rule .D [tm .bit0, nt .D]
  | .dKey1 => rule .D [tm .bit1, nt .D]
  | .dPayload0 => rule .D [tm .colon, tm .bit0, nt .E]
  | .dPayload1 => rule .D [tm .colon, tm .bit1, nt .E]
  | .ePayload0 => rule .E [tm .bit0, nt .E]
  | .ePayload1 => rule .E [tm .bit1, nt .E]
  | .eEnd => rule .E [tm .rangle, nt .A]
  | .rEnd => rule .R [tm .dollar]
  | .rRecord0 => rule .R [tm .langle, tm .bit0, nt .DPrime]
  | .rRecord1 => rule .R [tm .langle, tm .bit1, nt .DPrime]
  | .dPrimeKey0 => rule .DPrime [tm .bit0, nt .DPrime]
  | .dPrimeKey1 => rule .DPrime [tm .bit1, nt .DPrime]
  | .dPrimePayload0 => rule .DPrime [tm .colon, tm .bit0, nt .EPrime]
  | .dPrimePayload1 => rule .DPrime [tm .colon, tm .bit1, nt .EPrime]
  | .ePrimePayload0 => rule .EPrime [tm .bit0, nt .EPrime]
  | .ePrimePayload1 => rule .EPrime [tm .bit1, nt .EPrime]
  | .ePrimeEnd => rule .EPrime [tm .rangle, nt .R]
  | .kWrap0 => rule .K [tm .bit0, nt .K, tm .bit0]
  | .kWrap1 => rule .K [tm .bit1, nt .K, tm .bit1]
  | .kBase => rule .K [tm .colon, nt .P1, tm .hash]
  | .p0Base => rule .P0 [tm .rangle, nt .R]
  | .p000 => rule .P0 [tm .bit0, nt .P0, tm .bit0]
  | .p001 => rule .P0 [tm .bit0, nt .P0, tm .bit1]
  | .p010 => rule .P0 [tm .bit1, nt .P0, tm .bit0]
  | .p011 => rule .P0 [tm .bit1, nt .P1, tm .bit1]
  | .p100 => rule .P1 [tm .bit0, nt .P1, tm .bit0]
  | .p101 => rule .P1 [tm .bit0, nt .P1, tm .bit1]
  | .p110 => rule .P1 [tm .bit1, nt .P1, tm .bit0]
  | .p111 => rule .P1 [tm .bit1, nt .P0, tm .bit1]

def grammarRules : Finset (ContextFreeRule Terminal NT) :=
  Finset.univ.image production

@[reducible] def cfg : ContextFreeGrammar Terminal where
  NT := NT
  initial := .A
  rules := grammarRules

theorem nonterminal_card : Fintype.card NT = 9 := by decide

theorem alternative_card : Fintype.card RuleName = 33 := by decide

theorem grammarRules_card : grammarRules.card = 33 := by decide

theorem cfg_isLinear : cfg.IsLinear := by
  intro r hr
  rcases Finset.mem_image.mp hr with ⟨name, -, rfl⟩
  cases name <;>
    simp [ContextFreeRule.IsLinear, ContextFreeRule.outputNonterminals,
      production, rule, nt, tm]

private def terminalSymbols (w : Word) : Sentential :=
  w.map Symbol.terminal

private lemma production_mem (name : RuleName) :
    production name ∈ grammarRules := by
  simp [grammarRules]

private lemma production_derives (name : RuleName) :
    cfg.Derives [nt (production name).input] (production name).output := by
  apply ContextFreeGrammar.Produces.single
  exact ⟨production name, production_mem name,
    ContextFreeRule.Rewrites.input_output⟩

private lemma derives_in_context {u v : Sentential} (h : cfg.Derives u v)
    (pre post : Sentential) :
    cfg.Derives (pre ++ (u ++ post)) (pre ++ (v ++ post)) :=
  (h.append_right post).append_left pre


private lemma E.toLinearDerivesFrom (payloadTail : List Bit) {tail : Word}
    (hA : cfg.Derives [nt .A] (terminalSymbols tail)) :
    cfg.Derives [nt .E]
      (terminalSymbols (bitWord payloadTail ++ [.rangle] ++ tail)) := by
  induction payloadTail with
  | nil =>
      refine (production_derives .eEnd).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context hA [tm .rangle] []
  | cons b payloadTail ih =>
      cases b
      · refine (production_derives .ePayload0).trans ?_
        simpa [production, rule, nt, tm, terminalSymbols, bitTerminal, List.map_append,
          List.append_assoc] using
          derives_in_context ih [tm .bit0] []
      · refine (production_derives .ePayload1).trans ?_
        simpa [production, rule, nt, tm, terminalSymbols, bitTerminal, List.map_append,
          List.append_assoc] using
          derives_in_context ih [tm .bit1] []

private lemma D.toLinearDerivesFrom (keyTail payload : List Bit)
    (hpayload : payload ≠ []) {tail : Word}
    (hA : cfg.Derives [nt .A] (terminalSymbols tail)) :
    cfg.Derives [nt .D]
      (terminalSymbols
        (bitWord keyTail ++ [.colon] ++ bitWord payload ++
          [.rangle] ++ tail)) := by
  induction keyTail with
  | nil =>
      cases payload with
      | nil => exact (hpayload rfl).elim
      | cons b payloadTail =>
          have hE := E.toLinearDerivesFrom payloadTail hA
          cases b
          · refine (production_derives .dPayload0).trans ?_
            simpa [production, rule, nt, tm, terminalSymbols, bitTerminal, List.map_append,
              List.append_assoc] using
              derives_in_context hE [tm .colon, tm .bit0] []
          · refine (production_derives .dPayload1).trans ?_
            simpa [production, rule, nt, tm, terminalSymbols, bitTerminal, List.map_append,
              List.append_assoc] using
              derives_in_context hE [tm .colon, tm .bit1] []
  | cons b keyTail ih =>
      cases b
      · refine (production_derives .dKey0).trans ?_
        simpa [production, rule, nt, tm, terminalSymbols, bitTerminal, List.map_append,
          List.append_assoc] using
          derives_in_context ih [tm .bit0] []
      · refine (production_derives .dKey1).trans ?_
        simpa [production, rule, nt, tm, terminalSymbols, bitTerminal, List.map_append,
          List.append_assoc] using
          derives_in_context ih [tm .bit1] []

private lemma EPrime.toLinearDerivesFrom (payloadTail : List Bit)
    {tail : Word} (hR : cfg.Derives [nt .R] (terminalSymbols tail)) :
    cfg.Derives [nt .EPrime]
      (terminalSymbols (bitWord payloadTail ++ [.rangle] ++ tail)) := by
  induction payloadTail with
  | nil =>
      refine (production_derives .ePrimeEnd).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context hR [tm .rangle] []
  | cons b payloadTail ih =>
      cases b
      · refine (production_derives .ePrimePayload0).trans ?_
        simpa [production, rule, nt, tm, terminalSymbols, bitTerminal, List.map_append,
          List.append_assoc] using
          derives_in_context ih [tm .bit0] []
      · refine (production_derives .ePrimePayload1).trans ?_
        simpa [production, rule, nt, tm, terminalSymbols, bitTerminal, List.map_append,
          List.append_assoc] using
          derives_in_context ih [tm .bit1] []

private lemma DPrime.toLinearDerivesFrom (keyTail payload : List Bit)
    (hpayload : payload ≠ []) {tail : Word}
    (hR : cfg.Derives [nt .R] (terminalSymbols tail)) :
    cfg.Derives [nt .DPrime]
      (terminalSymbols
        (bitWord keyTail ++ [.colon] ++ bitWord payload ++
          [.rangle] ++ tail)) := by
  induction keyTail with
  | nil =>
      cases payload with
      | nil => exact (hpayload rfl).elim
      | cons b payloadTail =>
          have hE := EPrime.toLinearDerivesFrom payloadTail hR
          cases b
          · refine (production_derives .dPrimePayload0).trans ?_
            simpa [production, rule, nt, tm, terminalSymbols, bitTerminal, List.map_append,
              List.append_assoc] using
              derives_in_context hE [tm .colon, tm .bit0] []
          · refine (production_derives .dPrimePayload1).trans ?_
            simpa [production, rule, nt, tm, terminalSymbols, bitTerminal, List.map_append,
              List.append_assoc] using
              derives_in_context hE [tm .colon, tm .bit1] []
  | cons b keyTail ih =>
      cases b
      · refine (production_derives .dPrimeKey0).trans ?_
        simpa [production, rule, nt, tm, terminalSymbols, bitTerminal, List.map_append,
          List.append_assoc] using
          derives_in_context ih [tm .bit0] []
      · refine (production_derives .dPrimeKey1).trans ?_
        simpa [production, rule, nt, tm, terminalSymbols, bitTerminal, List.map_append,
          List.append_assoc] using
          derives_in_context ih [tm .bit1] []

private lemma R.toLinearDerivesRecords (rs : List Record)
    (hrs : ∀ r ∈ rs, r.Valid) :
    cfg.Derives [nt .R]
      (terminalSymbols (recordsWord rs ++ [.dollar])) := by
  induction rs with
  | nil =>
      simpa [production, rule, nt, tm, terminalSymbols] using
        production_derives .rEnd
  | cons r rs ih =>
      have hr : r.Valid := hrs r (by simp)
      have hrsTail : ∀ s ∈ rs, s.Valid := by
        intro s hs
        exact hrs s (by simp [hs])
      have hR := ih hrsTail
      rcases r with ⟨key, payload⟩
      rcases hr with ⟨hkey, hpayload⟩
      cases key with
      | nil => exact (hkey rfl).elim
      | cons b keyTail =>
          have hD :=
            DPrime.toLinearDerivesFrom keyTail payload hpayload hR
          cases b
          · refine (production_derives .rRecord0).trans ?_
            simpa [production, rule, nt, tm, terminalSymbols, recordsWord_cons,
              recordWord, bitWord, bitTerminal, List.map_append,
              List.append_assoc] using
              derives_in_context hD [tm .langle, tm .bit0] []
          · refine (production_derives .rRecord1).trans ?_
            simpa [production, rule, nt, tm, terminalSymbols, recordsWord_cons,
              recordWord, bitWord, bitTerminal, List.map_append,
              List.append_assoc] using
              derives_in_context hD [tm .langle, tm .bit1] []

private lemma pToLinearDerives {p : Bit} {w : Word} (h : P p w) :
    cfg.Derives [nt (if p then .P1 else .P0)] (terminalSymbols w) := by
  induction h with
  | base ht =>
      rcases ht.sound with ⟨rs, hrs, rfl⟩
      have hR := R.toLinearDerivesRecords rs hrs
      refine (production_derives .p0Base).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context hR [tm .rangle] []
  | zero00 _ ih =>
      refine (production_derives .p000).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context ih [tm .bit0] [tm .bit0]
  | zero01 _ ih =>
      refine (production_derives .p001).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context ih [tm .bit0] [tm .bit1]
  | zero10 _ ih =>
      refine (production_derives .p010).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context ih [tm .bit1] [tm .bit0]
  | zero11 _ ih =>
      refine (production_derives .p011).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context ih [tm .bit1] [tm .bit1]
  | one00 _ ih =>
      refine (production_derives .p100).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context ih [tm .bit0] [tm .bit0]
  | one01 _ ih =>
      refine (production_derives .p101).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context ih [tm .bit0] [tm .bit1]
  | one10 _ ih =>
      refine (production_derives .p110).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context ih [tm .bit1] [tm .bit0]
  | one11 _ ih =>
      refine (production_derives .p111).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context ih [tm .bit1] [tm .bit1]

private lemma kToLinearDerives {w : Word} (h : K w) :
    cfg.Derives [nt .K] (terminalSymbols w) := by
  induction h with
  | base hp =>
      refine (production_derives .kBase).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context (pToLinearDerives hp) [tm .colon] [tm .hash]
  | wrapZero _ ih =>
      refine (production_derives .kWrap0).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context ih [tm .bit0] [tm .bit0]
  | wrapOne _ ih =>
      refine (production_derives .kWrap1).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context ih [tm .bit1] [tm .bit1]

private lemma aToLinearDerives {w : Word} (h : A w) :
    cfg.Derives [nt .A] (terminalSymbols w) := by
  induction h with
  | skip he _ ih =>
      rcases he.sound with
        ⟨⟨key, payload⟩, ⟨hkey, hpayload⟩, rfl⟩
      cases key with
      | nil => exact (hkey rfl).elim
      | cons b keyTail =>
          have hD :=
            D.toLinearDerivesFrom keyTail payload hpayload ih
          cases b
          · refine (production_derives .aSkip0).trans ?_
            simpa [production, rule, nt, tm, terminalSymbols, recordWord,
              bitWord, bitTerminal, List.map_append, List.append_assoc] using
              derives_in_context hD [tm .langle, tm .bit0] []
          · refine (production_derives .aSkip1).trans ?_
            simpa [production, rule, nt, tm, terminalSymbols, recordWord,
              bitWord, bitTerminal, List.map_append, List.append_assoc] using
              derives_in_context hD [tm .langle, tm .bit1] []
  | witnessZero hk =>
      refine (production_derives .aWitness0).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context (kToLinearDerives hk)
          [tm .langle, tm .bit0] [tm .bit0]
  | witnessOne hk =>
      refine (production_derives .aWitness1).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context (kToLinearDerives hk)
          [tm .langle, tm .bit1] [tm .bit1]


def DMeaning (w : Word) : Prop :=
  ∃ (keyTail payload : List Bit) (tail : Word),
    payload ≠ [] ∧ A tail ∧
    w = bitWord keyTail ++ [.colon] ++ bitWord payload ++
      [.rangle] ++ tail

def EMeaning (w : Word) : Prop :=
  ∃ (payloadTail : List Bit) (tail : Word),
    A tail ∧
    w = bitWord payloadTail ++ [.rangle] ++ tail

def RMeaning (w : Word) : Prop :=
  ∃ t : Word, T t ∧ w = t ++ [.dollar]

def DPrimeMeaning (w : Word) : Prop :=
  ∃ (keyTail payload : List Bit) (t : Word),
    payload ≠ [] ∧ T t ∧
    w = bitWord keyTail ++ [.colon] ++ bitWord payload ++
      [.rangle] ++ t ++ [.dollar]

def EPrimeMeaning (w : Word) : Prop :=
  ∃ (payloadTail : List Bit) (t : Word),
    T t ∧
    w = bitWord payloadTail ++ [.rangle] ++ t ++ [.dollar]

def SymbolMeaning : GSymbol → Word → Prop
  | .terminal a, w => w = [a]
  | .nonterminal .A, w => A w
  | .nonterminal .D, w => DMeaning w
  | .nonterminal .E, w => EMeaning w
  | .nonterminal .R, w => RMeaning w
  | .nonterminal .DPrime, w => DPrimeMeaning w
  | .nonterminal .EPrime, w => EPrimeMeaning w
  | .nonterminal .K, w => K w
  | .nonterminal .P0, w => P false w
  | .nonterminal .P1, w => P true w

def SeqMeaning : Sentential → Word → Prop
  | [], w => w = []
  | s :: ss, w =>
      ∃ u v, w = u ++ v ∧ SymbolMeaning s u ∧ SeqMeaning ss v

private lemma SeqMeaning.append {u v : Sentential} {x y : Word}
    (hu : SeqMeaning u x) (hv : SeqMeaning v y) :
    SeqMeaning (u ++ v) (x ++ y) := by
  induction u generalizing x with
  | nil =>
      simp [SeqMeaning] at hu
      subst x
      simpa using hv
  | cons s ss ih =>
      rcases hu with ⟨a, b, rfl, ha, hb⟩
      refine ⟨a, b ++ y, by simp [List.append_assoc], ha, ?_⟩
      exact ih hb

private lemma SeqMeaning.split_append {u v : Sentential} {w : Word}
    (h : SeqMeaning (u ++ v) w) :
    ∃ x y, w = x ++ y ∧ SeqMeaning u x ∧ SeqMeaning v y := by
  induction u generalizing w with
  | nil =>
      exact ⟨[], w, by simp, rfl, by simpa using h⟩
  | cons s ss ih =>
      rcases h with ⟨a, b, rfl, ha, hb⟩
      rcases ih hb with ⟨x, y, rfl, hx, hy⟩
      exact
        ⟨a ++ x, y, by simp [List.append_assoc],
          ⟨a, x, rfl, ha, hx⟩, hy⟩

private lemma SeqMeaning.singleton {s : GSymbol} {w : Word}
    (h : SymbolMeaning s w) : SeqMeaning [s] w :=
  ⟨w, [], by simp, h, rfl⟩

private lemma seqMeaning_singleton_iff {s : GSymbol} {w : Word} :
    SeqMeaning [s] w ↔ SymbolMeaning s w := by
  simp [SeqMeaning]

private lemma terminalSymbols_meaning (w : Word) :
    SeqMeaning (terminalSymbols w) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      exact ⟨[a], w, rfl, rfl, ih⟩

private lemma terminalSymbols_meaning_iff (u w : Word) :
    SeqMeaning (terminalSymbols u) w ↔ w = u := by
  constructor
  · intro h
    induction u generalizing w with
    | nil =>
        simpa [terminalSymbols, SeqMeaning] using h
    | cons a u ih =>
        rcases h with ⟨x, y, hxy, hx, hy⟩
        have hx' : x = [a] := by
          simpa [terminalSymbols, SymbolMeaning] using hx
        have hy' : y = u := ih y hy
        subst x
        subst y
        simpa using hxy
  · rintro rfl
    exact terminalSymbols_meaning w

private lemma seqMeaning_linear_form (pre post : Word) (n : NT)
    {w : Word} :
    SeqMeaning
        (terminalSymbols pre ++ [nt n] ++ terminalSymbols post) w ↔
      ∃ middle, SymbolMeaning (nt n) middle ∧
        w = pre ++ middle ++ post := by
  constructor
  · intro h
    have h' :
        SeqMeaning
          (terminalSymbols pre ++
            ([nt n] ++ terminalSymbols post)) w := by
      simpa [List.append_assoc] using h
    rcases SeqMeaning.split_append
        (u := terminalSymbols pre)
        (v := [nt n] ++ terminalSymbols post) h' with
      ⟨x, rest, hword, hx, hrest⟩
    have hx' : x = pre := (terminalSymbols_meaning_iff pre x).mp hx
    subst x
    rcases SeqMeaning.split_append
        (u := [nt n]) (v := terminalSymbols post) hrest with
      ⟨middle, z, hrestWord, hmiddle, hz⟩
    have hmiddle' : SymbolMeaning (nt n) middle :=
      seqMeaning_singleton_iff.mp hmiddle
    have hz' : z = post :=
      (terminalSymbols_meaning_iff post z).mp hz
    subst z
    rw [hrestWord] at hword
    exact ⟨middle, hmiddle', by simpa [List.append_assoc] using hword⟩
  · rintro ⟨middle, hmiddle, rfl⟩
    have hpre := terminalSymbols_meaning pre
    have hmid := SeqMeaning.singleton hmiddle
    have hpost := terminalSymbols_meaning post
    simpa [List.append_assoc] using hpre.append (hmid.append hpost)

set_option linter.flexible false in
private lemma production_meaning (name : RuleName) {w : Word}
    (h : SeqMeaning (production name).output w) :
    SymbolMeaning (nt (production name).input) w := by
  cases name
  case aSkip0 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.langle, .bit0] ++ [nt .D] ++
            terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases
        (seqMeaning_linear_form [.langle, .bit0] [] .D).mp hs with
      ⟨u, hu, rfl⟩
    change DMeaning u at hu
    rcases hu with
      ⟨keyTail, payload, tail, hpayload, htail, rfl⟩
    change A _
    simpa [recordWord, bitWord, bitTerminal, List.append_assoc] using
      A.skip
        (E.complete ⟨false :: keyTail, payload⟩ ⟨by simp, hpayload⟩)
        htail
  case aSkip1 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.langle, .bit1] ++ [nt .D] ++
            terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases
        (seqMeaning_linear_form [.langle, .bit1] [] .D).mp hs with
      ⟨u, hu, rfl⟩
    change DMeaning u at hu
    rcases hu with
      ⟨keyTail, payload, tail, hpayload, htail, rfl⟩
    change A _
    simpa [recordWord, bitWord, bitTerminal, List.append_assoc] using
      A.skip
        (E.complete ⟨true :: keyTail, payload⟩ ⟨by simp, hpayload⟩)
        htail
  case aWitness0 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.langle, .bit0] ++ [nt .K] ++
            terminalSymbols [.bit0]) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases
        (seqMeaning_linear_form
          [.langle, .bit0] [.bit0] .K).mp hs with
      ⟨u, hu, rfl⟩
    change K u at hu
    change A _
    simpa [List.append_assoc] using A.witnessZero hu
  case aWitness1 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.langle, .bit1] ++ [nt .K] ++
            terminalSymbols [.bit1]) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases
        (seqMeaning_linear_form
          [.langle, .bit1] [.bit1] .K).mp hs with
      ⟨u, hu, rfl⟩
    change K u at hu
    change A _
    simpa [List.append_assoc] using A.witnessOne hu
  case dKey0 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit0] ++ [nt .D] ++ terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit0] [] .D).mp hs with
      ⟨u, hu, rfl⟩
    change DMeaning u at hu
    rcases hu with
      ⟨keyTail, payload, tail, hpayload, htail, rfl⟩
    change DMeaning _
    exact ⟨false :: keyTail, payload, tail, hpayload, htail, by
      simp [bitWord, bitTerminal, List.append_assoc]⟩
  case dKey1 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit1] ++ [nt .D] ++ terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit1] [] .D).mp hs with
      ⟨u, hu, rfl⟩
    change DMeaning u at hu
    rcases hu with
      ⟨keyTail, payload, tail, hpayload, htail, rfl⟩
    change DMeaning _
    exact ⟨true :: keyTail, payload, tail, hpayload, htail, by
      simp [bitWord, bitTerminal, List.append_assoc]⟩
  case dPayload0 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.colon, .bit0] ++ [nt .E] ++
            terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases
        (seqMeaning_linear_form [.colon, .bit0] [] .E).mp hs with
      ⟨u, hu, rfl⟩
    change EMeaning u at hu
    rcases hu with ⟨payloadTail, tail, htail, rfl⟩
    change DMeaning _
    exact ⟨[], false :: payloadTail, tail, by simp, htail, by
      simp [bitWord, bitTerminal, List.append_assoc]⟩
  case dPayload1 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.colon, .bit1] ++ [nt .E] ++
            terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases
        (seqMeaning_linear_form [.colon, .bit1] [] .E).mp hs with
      ⟨u, hu, rfl⟩
    change EMeaning u at hu
    rcases hu with ⟨payloadTail, tail, htail, rfl⟩
    change DMeaning _
    exact ⟨[], true :: payloadTail, tail, by simp, htail, by
      simp [bitWord, bitTerminal, List.append_assoc]⟩
  case ePayload0 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit0] ++ [nt .E] ++ terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit0] [] .E).mp hs with
      ⟨u, hu, rfl⟩
    change EMeaning u at hu
    rcases hu with ⟨payloadTail, tail, htail, rfl⟩
    change EMeaning _
    exact ⟨false :: payloadTail, tail, htail, by
      simp [bitWord, bitTerminal, List.append_assoc]⟩
  case ePayload1 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit1] ++ [nt .E] ++ terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit1] [] .E).mp hs with
      ⟨u, hu, rfl⟩
    change EMeaning u at hu
    rcases hu with ⟨payloadTail, tail, htail, rfl⟩
    change EMeaning _
    exact ⟨true :: payloadTail, tail, htail, by
      simp [bitWord, bitTerminal, List.append_assoc]⟩
  case eEnd =>
    have hs :
        SeqMeaning
          (terminalSymbols [.rangle] ++ [nt .A] ++ terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.rangle] [] .A).mp hs with
      ⟨tail, htail, rfl⟩
    change A tail at htail
    change EMeaning _
    exact ⟨[], tail, htail, by simp⟩
  case rEnd =>
    have hs : SeqMeaning (terminalSymbols [.dollar]) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    have hw : w = [.dollar] :=
      (terminalSymbols_meaning_iff [.dollar] w).mp hs
    subst w
    change RMeaning [.dollar]
    exact ⟨[], T.empty, rfl⟩
  case rRecord0 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.langle, .bit0] ++ [nt .DPrime] ++
            terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases
        (seqMeaning_linear_form
          [.langle, .bit0] [] .DPrime).mp hs with
      ⟨u, hu, rfl⟩
    change DPrimeMeaning u at hu
    rcases hu with ⟨keyTail, payload, t, hpayload, ht, rfl⟩
    change RMeaning _
    refine ⟨recordWord ⟨false :: keyTail, payload⟩ ++ t, ?_, ?_⟩
    · exact T.cons
        (E.complete ⟨false :: keyTail, payload⟩ ⟨by simp, hpayload⟩) ht
    · simp [recordWord, bitWord, bitTerminal, List.append_assoc]
  case rRecord1 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.langle, .bit1] ++ [nt .DPrime] ++
            terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases
        (seqMeaning_linear_form
          [.langle, .bit1] [] .DPrime).mp hs with
      ⟨u, hu, rfl⟩
    change DPrimeMeaning u at hu
    rcases hu with ⟨keyTail, payload, t, hpayload, ht, rfl⟩
    change RMeaning _
    refine ⟨recordWord ⟨true :: keyTail, payload⟩ ++ t, ?_, ?_⟩
    · exact T.cons
        (E.complete ⟨true :: keyTail, payload⟩ ⟨by simp, hpayload⟩) ht
    · simp [recordWord, bitWord, bitTerminal, List.append_assoc]
  case dPrimeKey0 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit0] ++ [nt .DPrime] ++
            terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit0] [] .DPrime).mp hs with
      ⟨u, hu, rfl⟩
    change DPrimeMeaning u at hu
    rcases hu with ⟨keyTail, payload, t, hpayload, ht, rfl⟩
    change DPrimeMeaning _
    exact ⟨false :: keyTail, payload, t, hpayload, ht, by
      simp [bitWord, bitTerminal, List.append_assoc]⟩
  case dPrimeKey1 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit1] ++ [nt .DPrime] ++
            terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit1] [] .DPrime).mp hs with
      ⟨u, hu, rfl⟩
    change DPrimeMeaning u at hu
    rcases hu with ⟨keyTail, payload, t, hpayload, ht, rfl⟩
    change DPrimeMeaning _
    exact ⟨true :: keyTail, payload, t, hpayload, ht, by
      simp [bitWord, bitTerminal, List.append_assoc]⟩
  case dPrimePayload0 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.colon, .bit0] ++ [nt .EPrime] ++
            terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases
        (seqMeaning_linear_form
          [.colon, .bit0] [] .EPrime).mp hs with
      ⟨u, hu, rfl⟩
    change EPrimeMeaning u at hu
    rcases hu with ⟨payloadTail, t, ht, rfl⟩
    change DPrimeMeaning _
    exact ⟨[], false :: payloadTail, t, by simp, ht, by
      simp [bitWord, bitTerminal, List.append_assoc]⟩
  case dPrimePayload1 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.colon, .bit1] ++ [nt .EPrime] ++
            terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases
        (seqMeaning_linear_form
          [.colon, .bit1] [] .EPrime).mp hs with
      ⟨u, hu, rfl⟩
    change EPrimeMeaning u at hu
    rcases hu with ⟨payloadTail, t, ht, rfl⟩
    change DPrimeMeaning _
    exact ⟨[], true :: payloadTail, t, by simp, ht, by
      simp [bitWord, bitTerminal, List.append_assoc]⟩
  case ePrimePayload0 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit0] ++ [nt .EPrime] ++
            terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit0] [] .EPrime).mp hs with
      ⟨u, hu, rfl⟩
    change EPrimeMeaning u at hu
    rcases hu with ⟨payloadTail, t, ht, rfl⟩
    change EPrimeMeaning _
    exact ⟨false :: payloadTail, t, ht, by
      simp [bitWord, bitTerminal, List.append_assoc]⟩
  case ePrimePayload1 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit1] ++ [nt .EPrime] ++
            terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit1] [] .EPrime).mp hs with
      ⟨u, hu, rfl⟩
    change EPrimeMeaning u at hu
    rcases hu with ⟨payloadTail, t, ht, rfl⟩
    change EPrimeMeaning _
    exact ⟨true :: payloadTail, t, ht, by
      simp [bitWord, bitTerminal, List.append_assoc]⟩
  case ePrimeEnd =>
    have hs :
        SeqMeaning
          (terminalSymbols [.rangle] ++ [nt .R] ++ terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.rangle] [] .R).mp hs with
      ⟨u, hu, rfl⟩
    change RMeaning u at hu
    rcases hu with ⟨t, ht, rfl⟩
    change EPrimeMeaning _
    exact ⟨[], t, ht, by simp⟩
  case kWrap0 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit0] ++ [nt .K] ++
            terminalSymbols [.bit0]) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit0] [.bit0] .K).mp hs with
      ⟨u, hu, rfl⟩
    change K u at hu
    change K _
    simpa [List.append_assoc] using K.wrapZero hu
  case kWrap1 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit1] ++ [nt .K] ++
            terminalSymbols [.bit1]) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit1] [.bit1] .K).mp hs with
      ⟨u, hu, rfl⟩
    change K u at hu
    change K _
    simpa [List.append_assoc] using K.wrapOne hu
  case kBase =>
    have hs :
        SeqMeaning
          (terminalSymbols [.colon] ++ [nt .P1] ++
            terminalSymbols [.hash]) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.colon] [.hash] .P1).mp hs with
      ⟨u, hu, rfl⟩
    change P true u at hu
    change K _
    simpa [List.append_assoc] using K.base hu
  case p0Base =>
    have hs :
        SeqMeaning
          (terminalSymbols [.rangle] ++ [nt .R] ++ terminalSymbols []) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.rangle] [] .R).mp hs with
      ⟨u, hu, rfl⟩
    change RMeaning u at hu
    rcases hu with ⟨t, ht, rfl⟩
    change P false _
    simpa [List.append_assoc] using P.base ht
  case p000 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit0] ++ [nt .P0] ++
            terminalSymbols [.bit0]) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit0] [.bit0] .P0).mp hs with
      ⟨u, hu, rfl⟩
    change P false u at hu
    change P false _
    simpa [List.append_assoc] using P.zero00 hu
  case p001 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit0] ++ [nt .P0] ++
            terminalSymbols [.bit1]) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit0] [.bit1] .P0).mp hs with
      ⟨u, hu, rfl⟩
    change P false u at hu
    change P false _
    simpa [List.append_assoc] using P.zero01 hu
  case p010 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit1] ++ [nt .P0] ++
            terminalSymbols [.bit0]) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit1] [.bit0] .P0).mp hs with
      ⟨u, hu, rfl⟩
    change P false u at hu
    change P false _
    simpa [List.append_assoc] using P.zero10 hu
  case p011 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit1] ++ [nt .P1] ++
            terminalSymbols [.bit1]) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit1] [.bit1] .P1).mp hs with
      ⟨u, hu, rfl⟩
    change P true u at hu
    change P false _
    simpa [List.append_assoc] using P.zero11 hu
  case p100 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit0] ++ [nt .P1] ++
            terminalSymbols [.bit0]) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit0] [.bit0] .P1).mp hs with
      ⟨u, hu, rfl⟩
    change P true u at hu
    change P true _
    simpa [List.append_assoc] using P.one00 hu
  case p101 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit0] ++ [nt .P1] ++
            terminalSymbols [.bit1]) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit0] [.bit1] .P1).mp hs with
      ⟨u, hu, rfl⟩
    change P true u at hu
    change P true _
    simpa [List.append_assoc] using P.one01 hu
  case p110 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit1] ++ [nt .P1] ++
            terminalSymbols [.bit0]) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit1] [.bit0] .P1).mp hs with
      ⟨u, hu, rfl⟩
    change P true u at hu
    change P true _
    simpa [List.append_assoc] using P.one10 hu
  case p111 =>
    have hs :
        SeqMeaning
          (terminalSymbols [.bit1] ++ [nt .P0] ++
            terminalSymbols [.bit1]) w := by
      simpa [production, rule, terminalSymbols, nt, tm] using h
    rcases (seqMeaning_linear_form [.bit1] [.bit1] .P0).mp hs with
      ⟨u, hu, rfl⟩
    change P false u at hu
    change P true _
    simpa [List.append_assoc] using P.one11 hu

private lemma produces_preserves_meaning {u v : Sentential} {w : Word}
    (huv : cfg.Produces u v) (hv : SeqMeaning v w) :
    SeqMeaning u w := by
  rcases huv with ⟨r, hr, hrewrite⟩
  rcases Finset.mem_image.mp hr with ⟨name, -, hname⟩
  rw [← hname] at hrewrite
  rcases hrewrite.exists_parts with ⟨pre, post, rfl, rfl⟩
  have hv' :
      SeqMeaning (pre ++ ((production name).output ++ post)) w := by
    simpa [List.append_assoc] using hv
  rcases SeqMeaning.split_append (u := pre)
      (v := (production name).output ++ post) hv' with
    ⟨wp, wrest, hword, hp, hrest⟩
  rw [hword]
  rcases SeqMeaning.split_append (u := (production name).output)
      (v := post) hrest with
    ⟨wr, wq, hrestWord, hright, hq⟩
  rw [hrestWord]
  have hleft : SymbolMeaning (nt (production name).input) wr :=
    production_meaning name hright
  have hmiddle : SeqMeaning [nt (production name).input] wr :=
    SeqMeaning.singleton hleft
  have hpmiddle :
      SeqMeaning (pre ++ [nt (production name).input]) (wp ++ wr) :=
    hp.append hmiddle
  simpa [nt, List.append_assoc] using hpmiddle.append hq

private lemma derives_preserves_meaning {u v : Sentential}
    (huv : cfg.Derives u v) {w : Word} (hv : SeqMeaning v w) :
    SeqMeaning u w := by
  induction huv with
  | refl => exact hv
  | tail _ hstep ih =>
      exact ih (produces_preserves_meaning hstep hv)

theorem mem_cfg_language_iff (w : Word) :
    w ∈ cfg.language ↔ A w := by
  rw [ContextFreeGrammar.mem_language_iff]
  constructor
  · intro h
    have hs : SeqMeaning [nt .A] w :=
      derives_preserves_meaning h (terminalSymbols_meaning w)
    simpa [SeqMeaning, SymbolMeaning, nt] using hs
  · exact fun h => aToLinearDerives h

theorem cfg_language_eq_C : cfg.language = C := by
  ext w
  exact
    (mem_cfg_language_iff w).trans
      (inductive_start_iff_mem_C w)

theorem C_isLinearContextFree :
    Language.IsLinearContextFree (C : Language Terminal) :=
  ⟨cfg, cfg_isLinear, cfg_language_eq_C⟩

theorem reverse_cfg_isLinear : cfg.reverse.IsLinear :=
  cfg_isLinear.reverse

theorem reverse_cfg_language_eq_L : cfg.reverse.language = L := by
  rw [ContextFreeGrammar.language_reverse, cfg_language_eq_C]
  rfl

theorem L_isLinearContextFree :
    Language.IsLinearContextFree (L : Language Terminal) := by
  change
    Language.IsLinearContextFree
      (Language.reverse (C : Language Terminal))
  exact C_isLinearContextFree.reverse

end LinearGrammar

end PegSeparation.Witness.LanguageCFG
