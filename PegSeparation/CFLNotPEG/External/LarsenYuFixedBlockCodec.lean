import PegSeparation.CFLNotPEG.External.LarsenYuSentinelPadding


namespace PegSeparation.External.LarsenYuFixedBlockCodec

open LarsenYuSentinelPadding

def paddedVector (width : Nat) (sentinel : α) (entries : List α)
    (hfit : entries.length ≤ width) : List.Vector α width :=
  ⟨padLeft width sentinel entries,
    length_padLeft_of_le width sentinel entries hfit⟩

def blockOfList (width : Nat) (sentinel : α) (entries : List α)
    (hfit : entries.length ≤ width) : Fin width → α :=
  (paddedVector width sentinel entries hfit).get

theorem ofFn_blockOfList (width : Nat) (sentinel : α) (entries : List α)
    (hfit : entries.length ≤ width) :
    List.ofFn (blockOfList width sentinel entries hfit) =
      padLeft width sentinel entries := by
  calc
    List.ofFn (blockOfList width sentinel entries hfit) =
        (List.Vector.ofFn (blockOfList width sentinel entries hfit)).toList := by
      symm
      exact List.Vector.toList_ofFn
        (blockOfList width sentinel entries hfit)
    _ = (paddedVector width sentinel entries hfit).toList := by
      rw [blockOfList, List.Vector.ofFn_get]
    _ = padLeft width sentinel entries := rfl

def encodeBlock (width : Nat) (sentinel : α) (entries : List α) :
    Fin width → α :=
  if hfit : entries.length ≤ width then
    blockOfList width sentinel entries hfit
  else fun _ ↦ sentinel

theorem encodeBlock_eq_blockOfList_of_le
    (width : Nat) (sentinel : α) (entries : List α)
    (hfit : entries.length ≤ width) :
    encodeBlock width sentinel entries =
      blockOfList width sentinel entries hfit := by
  simp only [encodeBlock, dif_pos hfit]

def decodeBlock [DecidableEq α] {width : Nat}
    (sentinel : α) (block : Fin width → α) :
    List α :=
  stripPrefix sentinel (List.ofFn block)

theorem decodeBlock_blockOfList [DecidableEq α]
    (width : Nat) (sentinel : α) (entries : List α)
    (hfit : entries.length ≤ width)
    (hentries : ∀ entry ∈ entries, entry ≠ sentinel) :
    decodeBlock sentinel (blockOfList width sentinel entries hfit) = entries := by
  rw [decodeBlock, ofFn_blockOfList]
  exact stripPrefix_padLeft width sentinel entries hentries

theorem decodeBlock_encodeBlock_of_le [DecidableEq α]
    (width : Nat) (sentinel : α) (entries : List α)
    (hfit : entries.length ≤ width)
    (hentries : ∀ entry ∈ entries, entry ≠ sentinel) :
    decodeBlock sentinel (encodeBlock width sentinel entries) = entries := by
  rw [encodeBlock_eq_blockOfList_of_le width sentinel entries hfit]
  exact decodeBlock_blockOfList width sentinel entries hfit hentries

theorem blockOfList_injective_on [DecidableEq α]
    (width : Nat) (sentinel : α)
    {left right : List α}
    (hleftFit : left.length ≤ width) (hrightFit : right.length ≤ width)
    (hleft : ∀ entry ∈ left, entry ≠ sentinel)
    (hright : ∀ entry ∈ right, entry ≠ sentinel)
    (hblocks : blockOfList width sentinel left hleftFit =
      blockOfList width sentinel right hrightFit) :
    left = right := by
  have hdecoded := congrArg (decodeBlock sentinel) hblocks
  simpa [decodeBlock_blockOfList width sentinel left hleftFit hleft,
    decodeBlock_blockOfList width sentinel right hrightFit hright] using hdecoded

end PegSeparation.External.LarsenYuFixedBlockCodec
