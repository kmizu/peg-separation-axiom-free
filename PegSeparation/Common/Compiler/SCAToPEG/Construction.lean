import PegSeparation.Common.Compiler.SCAToPEG.Support


namespace PegSeparation.SCAToPEG

open PegSeparation
open PegSeparation.Scaffolding

noncomputable section


def choices {Terminal : Type} {nonterminalCount : Nat} :
    List (ParsingExpression Terminal nonterminalCount) →
      ParsingExpression Terminal nonterminalCount
  | [] => .failure
  | expression :: expressions => .orderedChoice expression (choices expressions)

def sequences {Terminal : Type} {nonterminalCount : Nat} :
    List (ParsingExpression Terminal nonterminalCount) →
      ParsingExpression Terminal nonterminalCount
  | [] => .empty
  | expression :: expressions => .sequence expression (sequences expressions)


structure TransitionKey (Terminal : Type)
    (stateCount workLabelCount degree radius : Nat) where
  state : Fin stateCount
  symbol : Terminal
  view : Neighborhood (Fin workLabelCount) degree radius
  deriving DecidableEq, Fintype

inductive Name (stateCount workLabelCount degree radius : Nat) where
  | state (control : Fin stateCount)
  | label (work : Fin workLabelCount)
  | hood (view : Neighborhood (Fin workLabelCount) degree radius)
  | path (directions : BoundedPath degree radius)
  | consumeAll
  | accepts
  deriving DecidableEq, Fintype

noncomputable abbrev NameCount
    (stateCount workLabelCount degree radius : Nat) : Nat :=
  Fintype.card (Name stateCount workLabelCount degree radius)

noncomputable def nameEquiv
    (stateCount workLabelCount degree radius : Nat) :
    Name stateCount workLabelCount degree radius ≃
      Fin (NameCount stateCount workLabelCount degree radius) :=
  Fintype.equivFin _

noncomputable def encodeName
    {stateCount workLabelCount degree radius : Nat}
    (name : Name stateCount workLabelCount degree radius) :
    Fin (NameCount stateCount workLabelCount degree radius) :=
  nameEquiv stateCount workLabelCount degree radius name

noncomputable def decodeName
    {stateCount workLabelCount degree radius : Nat}
    (name : Fin (NameCount stateCount workLabelCount degree radius)) :
    Name stateCount workLabelCount degree radius :=
  (nameEquiv stateCount workLabelCount degree radius).symm name

@[simp] theorem decode_encodeName
    {stateCount workLabelCount degree radius : Nat}
    (name : Name stateCount workLabelCount degree radius) :
    decodeName (encodeName name) = name :=
  (nameEquiv stateCount workLabelCount degree radius).symm_apply_apply name

@[simp] theorem encode_decodeName
    {stateCount workLabelCount degree radius : Nat}
    (name : Fin (NameCount stateCount workLabelCount degree radius)) :
    encodeName (decodeName name) = name :=
  (nameEquiv stateCount workLabelCount degree radius).apply_symm_apply name

section Grammar

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
variable {stateCount workLabelCount degree radius : Nat}

local notation "Expr" =>
  ParsingExpression Terminal (NameCount stateCount workLabelCount degree radius)

noncomputable def invoke
    (name : Name stateCount workLabelCount degree radius) : Expr :=
  .nonterminal (encodeName name)

noncomputable def anyTerminal : Expr :=
  choices ((Finset.univ.toList : List Terminal).map ParsingExpression.terminal)

noncomputable def endOfInput : Expr :=
  .notPredicate (anyTerminal (Terminal := Terminal)
    (stateCount := stateCount) (workLabelCount := workLabelCount)
    (degree := degree) (radius := radius))

noncomputable def transitionTest
    (key : TransitionKey Terminal stateCount workLabelCount degree radius) : Expr :=
  .sequence
    (.andPredicate (.sequence (.terminal key.symbol) (invoke (.state key.state))))
    (.andPredicate (.sequence (.terminal key.symbol) (invoke (.hood key.view))))

noncomputable def dispatch
    (continuation : TransitionKey Terminal stateCount workLabelCount degree radius →
      Expr) : Expr :=
  choices ((Finset.univ.toList :
      List (TransitionKey Terminal stateCount workLabelCount degree radius)).map
    fun key => .sequence (transitionTest key) (continuation key))

noncomputable def actionFor
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (key : TransitionKey Terminal stateCount workLabelCount degree radius) :=
  automaton.transition key.state key.symbol key.view

noncomputable def stateRule
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (wanted : Fin stateCount) : Expr :=
  .orderedChoice
    (if wanted = automaton.initialState then endOfInput else .failure)
    (dispatch fun key =>
      if (actionFor automaton key).nextState = wanted then .empty else .failure)

noncomputable def labelRule
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (wanted : Fin workLabelCount) : Expr :=
  dispatch fun key =>
    if (actionFor automaton key).newLabel = wanted then .empty else .failure

noncomputable def pathLabelTest
    (path : BoundedPath degree radius) (label : Fin workLabelCount) : Expr :=
  .sequence (invoke (.path path)) (invoke (.label label))

noncomputable def observationConstraint
    (expected : Neighborhood (Fin workLabelCount) degree radius)
    (path : BoundedPath degree radius) : Expr :=
  match View.observe expected path with
  | none => .notPredicate (invoke (.path path))
  | some none =>
      .sequence
        (.andPredicate (invoke (.path path)))
        (sequences ((Finset.univ.toList : List (Fin workLabelCount)).map
          fun label => .notPredicate (pathLabelTest path label)))
  | some (some label) =>
      .sequence
        (.andPredicate (invoke (.path path)))
        (.andPredicate (pathLabelTest path label))

noncomputable def hoodRule
    (expected : Neighborhood (Fin workLabelCount) degree radius) : Expr :=
  sequences ((Finset.univ.toList : List (BoundedPath degree radius)).map
    (observationConstraint expected))

noncomputable def targetContinuation
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (key : TransitionKey Terminal stateCount workLabelCount degree radius)
    (direction : Fin degree) (tail : BoundedPath degree radius) : Expr :=
  match (actionFor automaton key).target direction with
  | .missing => .failure
  | .self => invoke (.path tail)
  | .path directions withinRadius =>
      .sequence (.terminal key.symbol)
        (.sequence
          (invoke (.path (boundedPathOfList directions withinRadius)))
          (invoke (.path tail)))

noncomputable def pathRule
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (path : BoundedPath degree radius) : Expr :=
  if empty : path.1 = [] then
    .empty
  else
    dispatch fun key =>
      targetContinuation automaton key (path.1.head empty) path.tail

noncomputable def consumeAllRule : Expr :=
  .orderedChoice
    (choices ((Finset.univ.toList : List Terminal).map fun symbol =>
      .sequence (.terminal symbol) (invoke .consumeAll)))
    .empty

noncomputable def acceptsRule
    (automaton : Automaton Terminal stateCount workLabelCount degree radius) : Expr :=
  .sequence
    (choices (automaton.accepting.toList.map fun state => invoke (.state state)))
    (invoke .consumeAll)

noncomputable def ruleFor
    (automaton : Automaton Terminal stateCount workLabelCount degree radius) :
    Name stateCount workLabelCount degree radius → Expr
  | .state control => stateRule automaton control
  | .label work => labelRule automaton work
  | .hood view => hoodRule view
  | .path directions => pathRule automaton directions
  | .consumeAll => consumeAllRule
  | .accepts => acceptsRule automaton

noncomputable def grammar
    (automaton : Automaton Terminal stateCount workLabelCount degree radius) :
    PegGrammar Terminal (NameCount stateCount workLabelCount degree radius) where
  rule name := ruleFor automaton (decodeName name)
  start := encodeName .accepts

@[simp] theorem grammar_rule_encode
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (name : Name stateCount workLabelCount degree radius) :
    (grammar automaton).rule (encodeName name) = ruleFor automaton name := by
  simp [grammar]

@[simp] theorem grammar_start
    (automaton : Automaton Terminal stateCount workLabelCount degree radius) :
    (grammar automaton).start = encodeName (.accepts :
      Name stateCount workLabelCount degree radius) := rfl

end Grammar

end

end PegSeparation.SCAToPEG
