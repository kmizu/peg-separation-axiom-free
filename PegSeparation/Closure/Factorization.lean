import PegSeparation.Closure.Definitions


namespace PegSeparation.Closure

open PegSeparation.Witness.LanguageCFG


private theorem mem_L_of_mem_mul {w : Word} (h : w ∈ Pref * RegularTail) :
    w ∈ (L : Language Terminal) := by
  rcases Language.mem_mul.mp h with ⟨u, hu, v, hv, rfl⟩
  rcases hu with ⟨r, rest, x, q, hr, hrest, hx, hq, hu, hkey, hlen, hip⟩
  rcases hv with ⟨ts, hts, rfl⟩
  refine ⟨ts.reverse ++ r :: rest, x, q, by simp, ?_, hx, hq, ?_, r, by simp,
    hkey, hlen, hip⟩
  · intro t ht
    simp only [List.mem_append, List.mem_reverse, List.mem_cons] at ht
    rcases ht with ht | rfl | ht
    · exact hts t ht
    · exact hr
    · exact hrest t ht
  · rw [List.reverse_append, reversedRecordsWord_reverse, hu, recordsWord_append,
      recordsWord_cons]
    simp [List.append_assoc]

private theorem mem_mul_of_mem_L {w : Word} (h : w ∈ (L : Language Terminal)) :
    w ∈ Pref * RegularTail := by
  rcases h with ⟨rs, x, q, -, hrs, hx, hq, hword, r, hrmem, hkey, hlen, hip⟩
  rcases List.append_of_mem hrmem with ⟨pre, post, rfl⟩
  have hpre : ∀ t ∈ pre, t.Valid := fun t ht => hrs t (by simp [ht])
  have hpost : ∀ t ∈ post, t.Valid := fun t ht => hrs t (by simp [ht])
  have hr : r.Valid := hrs r (by simp)
  refine Language.mem_mul.mpr
    ⟨bitWord q.reverse ++ [.hash] ++ bitWord x.reverse ++ [.dollar] ++
        reversedRecordsWord post.reverse ++ reversedRecordWord r,
      (mem_pref_iff_explicit _).mpr
        ⟨r, post, x, q, hr, hpost, hx, hq, rfl, hkey, hlen, hip⟩,
      (recordsWord pre).reverse, ⟨pre.reverse, ?_, recordsWord_reverse pre⟩, ?_⟩
  · intro t ht
    exact hpre t (List.mem_reverse.mp ht)
  · have hw : w = (recordsWord (pre ++ r :: post) ++ suffixWord x q).reverse := by
      rw [← hword, List.reverse_reverse]
    rw [hw, recordsWord_append, recordsWord_cons]
    simp [suffixWord, reversedRecordWord, recordsWord_reverse, List.append_assoc]


theorem witness_factorization :
    (PegSeparation.Witness.LanguageCFG.L :
      Language PegSeparation.Witness.LanguageCFG.Terminal) = Pref * RegularTail :=
  Set.ext fun _ => ⟨mem_mul_of_mem_L, mem_L_of_mem_mul⟩

end PegSeparation.Closure
