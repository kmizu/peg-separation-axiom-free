import Mathlib


variable {T N : Type*}

namespace ContextFreeRule

def outputNonterminals (r : ContextFreeRule T N) : List N :=
  r.output.filterMap fun
    | .terminal _ => none
    | .nonterminal n => some n

def IsLinear (r : ContextFreeRule T N) : Prop :=
  r.outputNonterminals.length ≤ 1

@[simp]
theorem outputNonterminals_reverse (r : ContextFreeRule T N) :
    r.reverse.outputNonterminals = r.outputNonterminals.reverse := by
  simp [outputNonterminals, ContextFreeRule.reverse]

protected theorem IsLinear.reverse {r : ContextFreeRule T N} (h : r.IsLinear) :
    r.reverse.IsLinear := by
  simpa [IsLinear] using h

@[simp]
theorem isLinear_reverse (r : ContextFreeRule T N) :
    r.reverse.IsLinear ↔ r.IsLinear :=
  ⟨fun h => by simpa using h.reverse, IsLinear.reverse⟩

end ContextFreeRule

namespace ContextFreeGrammar

def IsLinear (g : ContextFreeGrammar T) : Prop :=
  ∀ r ∈ g.rules, r.IsLinear

protected theorem IsLinear.reverse {g : ContextFreeGrammar T} (h : g.IsLinear) :
    g.reverse.IsLinear := by
  change ∀ r ∈ g.rules.map
    (⟨ContextFreeRule.reverse, ContextFreeRule.reverse_injective⟩ :
      ContextFreeRule T g.NT ↪ ContextFreeRule T g.NT), r.IsLinear
  rw [Finset.forall_mem_map]
  intro r hr
  exact (h r hr).reverse

@[simp]
theorem isLinear_reverse (g : ContextFreeGrammar T) :
    g.reverse.IsLinear ↔ g.IsLinear :=
  ⟨fun h => by simpa using h.reverse, IsLinear.reverse⟩

end ContextFreeGrammar

namespace Language

def IsLinearContextFree (L : Language T) : Prop :=
  ∃ g : ContextFreeGrammar T, g.IsLinear ∧ g.language = L

protected theorem IsLinearContextFree.isContextFree {L : Language T}
    (h : L.IsLinearContextFree) : L.IsContextFree := by
  rcases h with ⟨g, -, hlanguage⟩
  exact ⟨g, hlanguage⟩

protected theorem IsLinearContextFree.reverse {L : Language T}
    (h : L.IsLinearContextFree) : L.reverse.IsLinearContextFree := by
  rcases h with ⟨g, hg, rfl⟩
  exact ⟨g.reverse, hg.reverse, by simp⟩

@[simp]
theorem isLinearContextFree_reverse {L : Language T} :
    L.reverse.IsLinearContextFree ↔ L.IsLinearContextFree :=
  ⟨fun h => by simpa using h.reverse, IsLinearContextFree.reverse⟩

end Language
