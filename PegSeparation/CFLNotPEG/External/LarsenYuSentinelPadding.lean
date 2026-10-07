import Mathlib


namespace PegSeparation.External.LarsenYuSentinelPadding

def padLeft (width : Nat) (sentinel : α) (entries : List α) : List α :=
  List.replicate (width - entries.length) sentinel ++ entries

def stripPrefix [DecidableEq α] (sentinel : α) (block : List α) : List α :=
  block.dropWhile fun entry ↦ decide (entry = sentinel)

theorem stripPrefix_eq_self_of_forall_ne [DecidableEq α]
    (sentinel : α) (entries : List α)
    (hentries : ∀ entry ∈ entries, entry ≠ sentinel) :
    stripPrefix sentinel entries = entries := by
  induction entries with
  | nil => simp [stripPrefix]
  | cons head tail ih =>
      have hhead : head ≠ sentinel := hentries head (by simp)
      have htail : ∀ entry ∈ tail, entry ≠ sentinel := by
        intro entry hmem
        exact hentries entry (by simp [hmem])
      simp [stripPrefix, hhead]

theorem stripPrefix_padLeft [DecidableEq α]
    (width : Nat) (sentinel : α) (entries : List α)
    (hentries : ∀ entry ∈ entries, entry ≠ sentinel) :
    stripPrefix sentinel (padLeft width sentinel entries) = entries := by
  unfold stripPrefix padLeft
  rw [List.dropWhile_append_of_pos]
  · exact stripPrefix_eq_self_of_forall_ne sentinel entries hentries
  · intro entry hmem
    have heq : entry = sentinel := List.eq_of_mem_replicate hmem
    simp [heq]

theorem length_padLeft_of_le (width : Nat) (sentinel : α) (entries : List α)
    (hfit : entries.length ≤ width) :
    (padLeft width sentinel entries).length = width := by
  simp [padLeft, Nat.sub_add_cancel hfit]

theorem padLeft_injective_on
    (width : Nat) (sentinel : α)
    {left right : List α}
    (_hleftFit : left.length ≤ width) (_hrightFit : right.length ≤ width)
    (hleft : ∀ entry ∈ left, entry ≠ sentinel)
    (hright : ∀ entry ∈ right, entry ≠ sentinel)
    (hpadded : padLeft width sentinel left = padLeft width sentinel right) :
    left = right := by
  classical
  have hstripped := congrArg (stripPrefix sentinel) hpadded
  simpa [stripPrefix_padLeft width sentinel left hleft,
    stripPrefix_padLeft width sentinel right hright] using hstripped

theorem stripPrefix_twoBlocks [DecidableEq α]
    (width : Nat) (sentinel : α) (first second : List α)
    (hfirst : ∀ entry ∈ first, entry ≠ sentinel)
    (hsecond : ∀ entry ∈ second, entry ≠ sentinel) :
    (stripPrefix sentinel (padLeft width sentinel first),
      stripPrefix sentinel (padLeft width sentinel second)) = (first, second) := by
  simp [stripPrefix_padLeft width sentinel first hfirst,
    stripPrefix_padLeft width sentinel second hsecond]

end PegSeparation.External.LarsenYuSentinelPadding
