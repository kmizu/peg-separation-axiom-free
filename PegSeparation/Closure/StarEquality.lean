import PegSeparation.Closure.Definitions


namespace PegSeparation.Closure

open Computability
open PegSeparation.Witness.LanguageCFG


private lemma bitTerminal_ne_hash (b : Bit) : bitTerminal b ≠ Terminal.hash := by
  cases b <;> simp [bitTerminal]

private lemma bitTerminal_ne_rangle (b : Bit) : bitTerminal b ≠ Terminal.rangle := by
  cases b <;> simp [bitTerminal]

private lemma count_hash_bitWord (u : List Bit) :
    (bitWord u).count Terminal.hash = 0 := by
  refine List.count_eq_zero.mpr ?_
  intro hmem
  rcases List.mem_map.mp hmem with ⟨b, -, hb⟩
  exact bitTerminal_ne_hash b hb

private lemma count_hash_reversedRecordWord (r : Record) :
    (reversedRecordWord r).count Terminal.hash = 0 := by
  rw [reversedRecordWord_eq]
  simp [List.count_append, count_hash_bitWord]

private lemma count_hash_reversedRecordsWord (rs : List Record) :
    (reversedRecordsWord rs).count Terminal.hash = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      rw [reversedRecordsWord_cons, List.count_append, count_hash_reversedRecordWord, ih]

private lemma count_hash_of_mem_pref {w : Word} (hw : w ∈ Pref) :
    w.count Terminal.hash = 1 := by
  rcases (mem_pref_iff_explicit w).mp hw with ⟨r, rest, x, q, -, -, -, -, hword, -, -, -⟩
  rw [hword]
  simp [List.count_append, count_hash_bitWord, count_hash_reversedRecordsWord,
    count_hash_reversedRecordWord]

private lemma count_hash_of_mem_reversedRecord {w : Word} (hw : w ∈ ReversedRecord) :
    w.count Terminal.hash = 0 := by
  rcases hw with ⟨r, -, rfl⟩
  exact count_hash_reversedRecordWord r

private lemma count_hash_of_mem_shape {w : Word} (hw : w ∈ Shape) :
    w.count Terminal.hash = 1 := by
  rcases hw with ⟨a, b, rs, -, -, -, rfl⟩
  simp [List.count_append, count_hash_bitWord, count_hash_reversedRecordsWord]


private lemma head_of_mem_shape {w : Word} (hw : w ∈ Shape) :
    ∃ (b : Bit) (z : Word), w = bitTerminal b :: z := by
  rcases hw with ⟨a, b, rs, ha, -, -, rfl⟩
  cases a with
  | nil => exact absurd rfl ha
  | cons c a =>
      refine ⟨c, bitWord a ++ [Terminal.hash] ++ bitWord b ++ [Terminal.dollar] ++
        reversedRecordsWord rs, ?_⟩
      simp [List.append_assoc]

private lemma head_of_mem_reversedRecord {w : Word} (hw : w ∈ ReversedRecord) :
    ∃ z : Word, w = Terminal.rangle :: z := by
  rcases hw with ⟨r, -, rfl⟩
  refine ⟨bitWord r.payload.reverse ++ [Terminal.colon] ++ bitWord r.key.reverse ++
    [Terminal.langle], ?_⟩
  rw [reversedRecordWord_eq]
  simp [List.append_assoc]


private lemma reversedRecordsWord_eq_flatten (rs : List Record) :
    reversedRecordsWord rs = (rs.map reversedRecordWord).flatten := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [ih]

private lemma mem_reversedRecord_of_count_hash_zero {u : Word}
    (hu : u ∈ StarWitness) (h : u.count Terminal.hash = 0) : u ∈ ReversedRecord := by
  rcases (mem_starWitness_iff u).mp hu with hp | hr
  · rw [count_hash_of_mem_pref hp] at h
    exact absurd h one_ne_zero
  · exact hr

private lemma forall_reversedRecord_of_count_hash_zero (S : List Word)
    (hall : ∀ u ∈ S, u ∈ StarWitness)
    (hcount : S.flatten.count Terminal.hash = 0) :
    ∀ u ∈ S, u ∈ ReversedRecord := by
  induction S with
  | nil => intro u hu; simp at hu
  | cons v S ih =>
      rw [List.flatten_cons, List.count_append] at hcount
      have hv : v.count Terminal.hash = 0 := by omega
      have hs : S.flatten.count Terminal.hash = 0 := by omega
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact mem_reversedRecord_of_count_hash_zero (hall u (by simp)) hv
      · exact ih (fun t ht => hall t (by simp [ht])) hs u hu'

private lemma exists_records_of_forall_reversedRecord (S : List Word)
    (hall : ∀ u ∈ S, u ∈ ReversedRecord) :
    ∃ ts : List Record, (∀ t ∈ ts, t.Valid) ∧ S.flatten = reversedRecordsWord ts := by
  induction S with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons v S ih =>
      rcases hall v (by simp) with ⟨r, hr, rfl⟩
      rcases ih (fun t ht => hall t (by simp [ht])) with ⟨ts, hts, hflat⟩
      refine ⟨r :: ts, ?_, ?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact hr
        · exact hts t ht'
      · rw [List.flatten_cons, hflat, reversedRecordsWord_cons]


theorem starWitness_kstar_inter_shape :
    (StarWitness∗ ⊓ Shape : Language Terminal) =
      (PegSeparation.Witness.LanguageCFG.L : Language Terminal) := by
  ext w
  rw [Language.mem_inf]
  constructor
  · rintro ⟨hstar, hshape⟩
    rcases Language.mem_kstar.mp hstar with ⟨S, hflat, hmem⟩
    obtain ⟨b₀, z₀, hz₀⟩ := head_of_mem_shape hshape
    cases S with
    | nil =>
        rw [hz₀] at hflat
        simp at hflat
    | cons u S =>
        have hu : u ∈ StarWitness := hmem u (by simp)
        have hupref : u ∈ Pref := by
          rcases (mem_starWitness_iff u).mp hu with hp | hr
          · exact hp
          · exfalso
            obtain ⟨z₁, hz₁⟩ := head_of_mem_reversedRecord hr
            rw [hz₀, List.flatten_cons, hz₁] at hflat
            simp only [List.cons_append, List.cons.injEq] at hflat
            exact bitTerminal_ne_rangle b₀ hflat.1
        have hcount : (u ++ S.flatten).count Terminal.hash = 1 := by
          rw [← List.flatten_cons, ← hflat]
          exact count_hash_of_mem_shape hshape
        rw [List.count_append, count_hash_of_mem_pref hupref] at hcount
        have hzero : S.flatten.count Terminal.hash = 0 := by omega
        obtain ⟨ts, hts, htsword⟩ :=
          exists_records_of_forall_reversedRecord S
            (forall_reversedRecord_of_count_hash_zero S
              (fun v hv => hmem v (by simp [hv])) hzero)
        have hw : w = u ++ reversedRecordsWord ts := by
          rw [hflat, List.flatten_cons, htsword]
        obtain ⟨r, rest, x, q, hr, hrest, hx, hq, hpword, hkey, hlen, hip⟩ := hupref
        refine ⟨ts.reverse ++ r :: rest, x, q, by simp, ?_, hx, hq, ?_,
          r, by simp, hkey, hlen, hip⟩
        · intro t ht
          rcases List.mem_append.mp ht with ht' | ht'
          · exact hts t (List.mem_reverse.mp ht')
          · rcases List.mem_cons.mp ht' with rfl | ht''
            · exact hr
            · exact hrest t ht''
        · rw [hw, List.reverse_append, reversedRecordsWord_reverse, hpword,
            recordsWord_append, List.append_assoc]
  · intro hw
    obtain ⟨rs, x, q, -, hrs, hx, hq, hword, r, hrmem, hkey, hlen, hip⟩ := hw
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hrmem
    have hrvalid : r.Valid := hrs r (by simp)
    have hpre : ∀ t ∈ pre, t.Valid := fun t ht => hrs t (by simp [ht])
    have hpost : ∀ t ∈ post, t.Valid := fun t ht => hrs t (by simp [ht])
    have hdecomp : w =
        (bitWord q.reverse ++ [Terminal.hash] ++ bitWord x.reverse ++ [Terminal.dollar] ++
          reversedRecordsWord post.reverse ++ reversedRecordWord r) ++
          reversedRecordsWord pre.reverse := by
      have h := congrArg List.reverse hword
      rw [List.reverse_reverse] at h
      rw [h]
      simp [suffixWord, recordsWord_reverse, List.append_assoc]
    set p : Word :=
      bitWord q.reverse ++ [Terminal.hash] ++ bitWord x.reverse ++ [Terminal.dollar] ++
        reversedRecordsWord post.reverse ++ reversedRecordWord r with hp
    have hpmem : p ∈ Pref :=
      (mem_pref_iff_explicit p).mpr ⟨r, post, x, q, hrvalid, hpost, hx, hq, hp, hkey, hlen, hip⟩
    refine ⟨Language.mem_kstar.mpr ⟨p :: pre.reverse.map reversedRecordWord, ?_, ?_⟩, ?_⟩
    · rw [List.flatten_cons, ← reversedRecordsWord_eq_flatten]
      exact hdecomp
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact (mem_starWitness_iff _).mpr (Or.inl hpmem)
      · rcases List.mem_map.mp hv' with ⟨t, ht, rfl⟩
        exact (mem_starWitness_iff _).mpr
          (Or.inr ⟨t, hpre t (List.mem_reverse.mp ht), rfl⟩)
    · refine ⟨q.reverse, x.reverse, (pre ++ r :: post).reverse, by simpa using hq,
        by simpa using hx, ?_, ?_⟩
      · intro t ht
        exact hrs t (List.mem_reverse.mp ht)
      · rw [hdecomp, hp]
        simp [List.append_assoc]

end PegSeparation.Closure
