import PegSeparation.CFLNotPEG.External.LarsenYuConditionalJensen


open scoped BigOperators

namespace PegSeparation.External.LarsenYuTruncation

noncomputable section

open LarsenYuConditionalJensen

def overflowCollapsed
    {Input Message : Type} (message : Input → Message)
    (overflow : Input → Prop) [DecidablePred overflow] :
    Input → Option Message :=
  fun input ↦ if overflow input then none else some (message input)

theorem partitionL1_le_overflowCollapsed_add_mass
    {Input Message : Type} [Fintype Input] [Fintype Message]
    [DecidableEq Message]
    (weight signal : Input → ℝ) (message : Input → Message)
    (overflow : Input → Prop) [DecidablePred overflow]
    (hweight : ∀ input, 0 ≤ weight input)
    (hsignal : ∀ input, |signal input| ≤ 1) :
    (∑ originalMessage : Message,
      |∑ input, weight input *
        (if message input = originalMessage then signal input else 0)|) ≤
      (∑ collapsedMessage : Option Message,
        |∑ input, weight input *
          (if overflowCollapsed message overflow input = collapsedMessage
            then signal input else 0)|) +
      ∑ input, weight input * if overflow input then 1 else 0 := by
  classical
  let keptContribution (originalMessage : Message) : ℝ :=
    ∑ input, weight input *
      (if message input = originalMessage ∧ ¬overflow input
        then signal input else 0)
  let lostContribution (originalMessage : Message) : ℝ :=
    ∑ input, weight input *
      (if message input = originalMessage ∧ overflow input
        then signal input else 0)
  have hsplit (originalMessage : Message) :
      (∑ input, weight input *
        (if message input = originalMessage then signal input else 0)) =
        keptContribution originalMessage + lostContribution originalMessage := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro input _
    by_cases hmessage : message input = originalMessage
    · by_cases hoverflow : overflow input <;>
        simp [hmessage, hoverflow]
    · simp [hmessage]
  have hcollapsedSome (originalMessage : Message) :
      (∑ input, weight input *
        (if overflowCollapsed message overflow input = some originalMessage
          then signal input else 0)) = keptContribution originalMessage := by
    apply Finset.sum_congr rfl
    intro input _
    by_cases hoverflow : overflow input
    · simp [overflowCollapsed, hoverflow]
    · by_cases hmessage : message input = originalMessage <;>
        simp [overflowCollapsed, hoverflow, hmessage]
  have hkept :
      (∑ originalMessage : Message, |keptContribution originalMessage|) ≤
        ∑ collapsedMessage : Option Message,
          |∑ input, weight input *
            (if overflowCollapsed message overflow input = collapsedMessage
              then signal input else 0)| := by
    rw [Fintype.sum_option]
    simp_rw [hcollapsedSome]
    exact le_add_of_nonneg_left (abs_nonneg _)
  have hlost :
      (∑ originalMessage : Message, |lostContribution originalMessage|) ≤
        ∑ input, weight input * if overflow input then 1 else 0 := by
    calc
      (∑ originalMessage : Message, |lostContribution originalMessage|) ≤
          ∑ originalMessage : Message, ∑ input,
            |weight input *
              (if message input = originalMessage ∧ overflow input
                then signal input else 0)| := by
        apply Finset.sum_le_sum
        intro originalMessage _
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ originalMessage : Message, ∑ input,
          weight input *
            (if message input = originalMessage ∧ overflow input
              then 1 else 0) := by
        apply Finset.sum_le_sum
        intro originalMessage _
        apply Finset.sum_le_sum
        intro input _
        by_cases hcondition :
            message input = originalMessage ∧ overflow input
        · simp only [hcondition, abs_mul,
            abs_of_nonneg (hweight input)]
          exact mul_le_mul_of_nonneg_left (hsignal input) (hweight input)
        · simp [hcondition]
      _ = ∑ input, ∑ originalMessage : Message,
          weight input *
            (if message input = originalMessage ∧ overflow input
              then 1 else 0) := Finset.sum_comm
      _ = ∑ input, weight input * if overflow input then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro input _
        by_cases hoverflow : overflow input
        · rw [Fintype.sum_eq_single (message input)]
          · simp [hoverflow]
          · intro other hne
            simp [hoverflow, hne.symm]
        · simp [hoverflow]
  calc
    (∑ originalMessage : Message,
      |∑ input, weight input *
        (if message input = originalMessage then signal input else 0)|) =
        ∑ originalMessage : Message,
          |keptContribution originalMessage +
            lostContribution originalMessage| := by
      apply Finset.sum_congr rfl
      intro originalMessage _
      rw [hsplit]
    _ ≤ ∑ originalMessage : Message,
        (|keptContribution originalMessage| +
          |lostContribution originalMessage|) := by
      apply Finset.sum_le_sum
      intro originalMessage _
      exact abs_add_le _ _
    _ = (∑ originalMessage : Message, |keptContribution originalMessage|) +
        ∑ originalMessage : Message, |lostContribution originalMessage| := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ collapsedMessage : Option Message,
        |∑ input, weight input *
          (if overflowCollapsed message overflow input = collapsedMessage
            then signal input else 0)|) +
        ∑ input, weight input * if overflow input then 1 else 0 :=
      add_le_add hkept hlost

theorem partitionL1_sub_overflowMass_le_of_recover
    {Input Message Capped : Type}
    [Fintype Input] [Fintype Message] [Fintype Capped]
    [DecidableEq Message] [DecidableEq Capped]
    (weight signal : Input → ℝ)
    (message : Input → Message) (capped : Input → Capped)
    (overflow : Input → Prop) [DecidablePred overflow]
    (recover : Capped → Option Message)
    (hrecover : ∀ input,
      recover (capped input) = overflowCollapsed message overflow input)
    (hweight : ∀ input, 0 ≤ weight input)
    (hsignal : ∀ input, |signal input| ≤ 1) :
    (∑ originalMessage : Message,
      |∑ input, weight input *
        (if message input = originalMessage then signal input else 0)|) -
      (∑ input, weight input * if overflow input then 1 else 0) ≤
      ∑ cappedMessage : Capped,
        |∑ input, weight input *
          (if capped input = cappedMessage then signal input else 0)| := by
  have hcollapse :=
    partitionL1_mono_of_factor weight signal
      (overflowCollapsed message overflow) capped recover hrecover
  have hloss :=
    partitionL1_le_overflowCollapsed_add_mass
      weight signal message overflow hweight hsignal
  linarith

end

end PegSeparation.External.LarsenYuTruncation
