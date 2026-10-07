import PegSeparation.Closure.WordHom
import PegSeparation.External.PartialTotalization.TotalityHelpers

/-!
# Inverse images under nonerasing homomorphisms: the simulating grammar

Fix a grammar `g` over `Target` and a nonerasing homomorphism `hom : Source → List Target`.
The simulating grammar reads a source word while simulating `g` on its image.

A **state** `q : St Source` is a position inside the image: `none` is a block boundary (the next
source letter is still unread), and `some (a, i)` with `0 < i < |hom a|` is offset `i` inside the
block of the letter `a`, which was already read. The image still to be read at state `q` with
source `u` is `img hom q u`.

The new grammar has one rule per **item** `(e, q, q')`: a subexpression `e` of `g` started at
state `q` and required to end at state `q'`. The rule succeeds, consuming the source between the
two positions, exactly when `e` succeeds on the image and ends at state `q'`. Failure of `e` is
tested as "no end state works".
-/

namespace PegSeparation.Closure.InverseImageNonerasing

open PegSeparation PegSeparation.PegGrammar

/-- A position inside the image of a source word. -/
abbrev St (Source : Type) := Option (Source × ℕ)

/-- The ordered choice over a list, ending in failure. -/
def chain {α T : Type} {n : ℕ} : List α → (α → ParsingExpression T n) → ParsingExpression T n
  | [], _ => .failure
  | y :: l, F => .orderedChoice (F y) (chain l F)

/-- `ε` when the two states agree, failure otherwise. -/
def guardEq {Source T : Type} [DecidableEq Source] {n : ℕ} (q q' : St Source) :
    ParsingExpression T n :=
  if q' = q then .empty else .failure

/-- The outcome expected at end state `q'` when the run ends at state `q₁` with source rest `u₁`. -/
def outcome {Source : Type} [DecidableEq Source] (q₁ : St Source) (u₁ : List Source)
    (q' : St Source) : ParseResult Source :=
  if q' = q₁ then .success u₁ else .failure

/-- The subexpressions of an expression, itself first. -/
def subs {T : Type} {n : ℕ} : ParsingExpression T n → List (ParsingExpression T n)
  | .sequence a b => .sequence a b :: (subs a ++ subs b)
  | .orderedChoice a b => .orderedChoice a b :: (subs a ++ subs b)
  | .notPredicate a => .notPredicate a :: subs a
  | .andPredicate a => .andPredicate a :: subs a
  | e => [e]

section Defs

variable {Source Target : Type} [Fintype Source] [DecidableEq Source] [DecidableEq Target]
  {m : ℕ}

variable (hom : WordHom Source Target) (g : PegGrammar Target m)

/-- The image still to be read at a state with source `u`. -/
def img : St Source → List Source → List Target
  | none, u => hom.extend u
  | some (a, i), u => (hom.letterImage a).drop i ++ hom.extend u

/-- All source letters. -/
noncomputable def letters : List Source := (Finset.univ : Finset Source).toList

/-- All states. -/
noncomputable def stList : List (St Source) :=
  none :: (letters (Source := Source)).flatMap
    (fun a => (List.range ((hom.letterImage a).length - 1)).map (fun j => some (a, j + 1)))

/-- The state after the image letter at offset `i` of the block of `a`. -/
def nextSt (a : Source) (i : ℕ) : St Source :=
  if i + 1 < (hom.letterImage a).length then some (a, i + 1) else none

/-- The subexpressions of all rules of `g`. -/
def closure : List (ParsingExpression Target m) :=
  (List.finRange m).flatMap (fun i => subs (g.rule i))

/-- An item: a subexpression with its start and end states. -/
abbrev Item (Source Target : Type) (m : ℕ) :=
  ParsingExpression Target m × St Source × St Source

/-- All items. -/
noncomputable def items : List (Item Source Target m) :=
  (closure g).flatMap (fun e => (stList hom).flatMap
    (fun q => (stList hom).map (fun q' => (e, q, q'))))

/-- The number of nonterminals of the simulating grammar (one junk rule at the end). -/
noncomputable def count : ℕ := (items hom g).length + 1

open Classical in
/-- The rule index of an item (the junk index for non-items). -/
noncomputable def code (x : Item Source Target m) : Fin (count hom g) :=
  if h : x ∈ items hom g then
    ⟨(items hom g).idxOf x, by
      have := List.idxOf_lt_length_iff.mpr h
      unfold count; omega⟩
  else ⟨(items hom g).length, by unfold count; omega⟩

/-- The call of an item. -/
noncomputable def N (x : Item Source Target m) : ParsingExpression Source (count hom g) :=
  .nonterminal (code hom g x)

/-- `e` fails from `q`: no end state works. -/
noncomputable def FL (e : ParsingExpression Target m) (q : St Source) :
    ParsingExpression Source (count hom g) :=
  .notPredicate (chain (stList hom) (fun y => N hom g (e, q, y)))

/-- Read the image letter `c` from state `q` to state `q'`. -/
noncomputable def step1 (c : Target) : St Source → St Source →
    ParsingExpression Source (count hom g)
  | some (a, i), q' =>
      if (hom.letterImage a)[i]? = some c ∧ nextSt hom a i = q' then .empty else .failure
  | none, q' => chain (letters (Source := Source))
      (fun a => if (hom.letterImage a)[0]? = some c ∧ nextSt hom a 0 = q'
        then .terminal a else .failure)

/-- The rule of an item. -/
noncomputable def body : Item Source Target m → ParsingExpression Source (count hom g)
  | (.empty, q, q') => guardEq q q'
  | (.failure, _, _) => .failure
  | (.terminal c, q, q') => step1 hom g c q q'
  | (.nonterminal i, q, q') => N hom g (g.rule i, q, q')
  | (.sequence e₁ e₂, q, q') =>
      chain (stList hom) (fun y => .sequence (N hom g (e₁, q, y)) (N hom g (e₂, y, q')))
  | (.orderedChoice e₁ e₂, q, q') =>
      .orderedChoice (N hom g (e₁, q, q')) (.sequence (FL hom g e₁ q) (N hom g (e₂, q, q')))
  | (.notPredicate e, q, q') => .sequence (FL hom g e q) (guardEq q q')
  | (.andPredicate e, q, q') =>
      .sequence (.andPredicate (chain (stList hom) (fun y => N hom g (e, q, y)))) (guardEq q q')

/-- **The simulating grammar.** -/
noncomputable def grammar : PegGrammar Source (count hom g) where
  rule j := if h : j.val < (items hom g).length then body hom g (items hom g)[j.val] else .failure
  start := code hom g (g.rule g.start, none, none)

end Defs

end PegSeparation.Closure.InverseImageNonerasing
