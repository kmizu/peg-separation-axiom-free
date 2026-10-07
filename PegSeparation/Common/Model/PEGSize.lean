import PegSeparation.Common.Model.PEG


namespace PegSeparation

namespace ParsingExpression

variable {Terminal : Type} {nonterminalCount : Nat}

def coreNodeCount :
    ParsingExpression Terminal nonterminalCount → Nat
  | .empty => 1
  | .failure => 1
  | .terminal _ => 1
  | .nonterminal _ => 1
  | .sequence left right =>
      1 + left.coreNodeCount + right.coreNodeCount
  | .orderedChoice left right =>
      1 + left.coreNodeCount + right.coreNodeCount
  | .notPredicate body =>
      1 + body.coreNodeCount
  | .andPredicate body =>
      1 + body.coreNodeCount

@[simp] theorem coreNodeCount_empty :
    (ParsingExpression.empty :
      ParsingExpression Terminal nonterminalCount).coreNodeCount = 1 :=
  rfl

@[simp] theorem coreNodeCount_failure :
    (ParsingExpression.failure :
      ParsingExpression Terminal nonterminalCount).coreNodeCount = 1 :=
  rfl

@[simp] theorem coreNodeCount_terminal (symbol : Terminal) :
    (ParsingExpression.terminal symbol :
      ParsingExpression Terminal nonterminalCount).coreNodeCount = 1 :=
  rfl

@[simp] theorem coreNodeCount_nonterminal
    (name : Fin nonterminalCount) :
    (ParsingExpression.nonterminal name :
      ParsingExpression Terminal nonterminalCount).coreNodeCount = 1 :=
  rfl

@[simp] theorem coreNodeCount_sequence
    (left right : ParsingExpression Terminal nonterminalCount) :
    (ParsingExpression.sequence left right).coreNodeCount =
      1 + left.coreNodeCount + right.coreNodeCount :=
  rfl

@[simp] theorem coreNodeCount_orderedChoice
    (left right : ParsingExpression Terminal nonterminalCount) :
    (ParsingExpression.orderedChoice left right).coreNodeCount =
      1 + left.coreNodeCount + right.coreNodeCount :=
  rfl

@[simp] theorem coreNodeCount_notPredicate
    (body : ParsingExpression Terminal nonterminalCount) :
    (ParsingExpression.notPredicate body).coreNodeCount =
      1 + body.coreNodeCount :=
  rfl

@[simp] theorem coreNodeCount_andPredicate
    (body : ParsingExpression Terminal nonterminalCount) :
    (ParsingExpression.andPredicate body).coreNodeCount =
      1 + body.coreNodeCount :=
  rfl

theorem coreNodeCount_pos
    (expression : ParsingExpression Terminal nonterminalCount) :
    0 < expression.coreNodeCount := by
  induction expression <;> simp_all [coreNodeCount]

inductive StructuralKey (Terminal : Type) (nonterminalCount : Nat) where
  | empty
  | failure
  | terminal (symbol : Terminal)
  | nonterminal (name : Fin nonterminalCount)
  | sequence (left right : StructuralKey Terminal nonterminalCount)
  | orderedChoice (left right : StructuralKey Terminal nonterminalCount)
  | notPredicate (body : StructuralKey Terminal nonterminalCount)
  | andPredicate (body : StructuralKey Terminal nonterminalCount)
  deriving DecidableEq, Repr

def structuralKey :
    ParsingExpression Terminal nonterminalCount →
      StructuralKey Terminal nonterminalCount
  | .empty => .empty
  | .failure => .failure
  | .terminal symbol => .terminal symbol
  | .nonterminal name => .nonterminal name
  | .sequence left right =>
      .sequence left.structuralKey right.structuralKey
  | .orderedChoice left right =>
      .orderedChoice left.structuralKey right.structuralKey
  | .notPredicate body => .notPredicate body.structuralKey
  | .andPredicate body => .andPredicate body.structuralKey

def subexpressionKeys [DecidableEq Terminal]
    (expression : ParsingExpression Terminal nonterminalCount) :
    Finset (StructuralKey Terminal nonterminalCount) :=
  match expression with
  | .empty => {expression.structuralKey}
  | .failure => {expression.structuralKey}
  | .terminal _ => {expression.structuralKey}
  | .nonterminal _ => {expression.structuralKey}
  | .sequence left right =>
      insert expression.structuralKey
        (left.subexpressionKeys ∪ right.subexpressionKeys)
  | .orderedChoice left right =>
      insert expression.structuralKey
        (left.subexpressionKeys ∪ right.subexpressionKeys)
  | .notPredicate body =>
      insert expression.structuralKey body.subexpressionKeys
  | .andPredicate body =>
      insert expression.structuralKey body.subexpressionKeys

def hashConsedCoreNodeCount [DecidableEq Terminal]
    (expression : ParsingExpression Terminal nonterminalCount) : Nat :=
  expression.subexpressionKeys.card

end ParsingExpression

structure PegSizeStatistics where
  nonterminalCount : Nat
  coreNodeCount : Nat
  hashConsedCoreNodeCount : Nat
  deriving DecidableEq, Repr

namespace PegSizeStatistics

def ruleSharedTotal (statistics : PegSizeStatistics) : Nat :=
  statistics.nonterminalCount + statistics.coreNodeCount

def hashConsedTotal (statistics : PegSizeStatistics) : Nat :=
  statistics.nonterminalCount + statistics.hashConsedCoreNodeCount

end PegSizeStatistics

namespace PegGrammar

variable {Terminal : Type} {nonterminalCount : Nat}

def ruleCoreNodeCount
    (grammar : PegGrammar Terminal nonterminalCount)
    (name : Fin nonterminalCount) : Nat :=
  (grammar.rule name).coreNodeCount

def coreNodeCount
    (grammar : PegGrammar Terminal nonterminalCount) : Nat :=
  ∑ name : Fin nonterminalCount, grammar.ruleCoreNodeCount name

def coreSubexpressionKeys [DecidableEq Terminal]
    (grammar : PegGrammar Terminal nonterminalCount) :
    Finset (ParsingExpression.StructuralKey Terminal nonterminalCount) :=
  Finset.univ.biUnion fun name => (grammar.rule name).subexpressionKeys

def hashConsedCoreNodeCount [DecidableEq Terminal]
    (grammar : PegGrammar Terminal nonterminalCount) : Nat :=
  grammar.coreSubexpressionKeys.card

def sizeStatistics [DecidableEq Terminal]
    (grammar : PegGrammar Terminal nonterminalCount) : PegSizeStatistics where
  nonterminalCount := nonterminalCount
  coreNodeCount := grammar.coreNodeCount
  hashConsedCoreNodeCount := grammar.hashConsedCoreNodeCount

@[simp] theorem sizeStatistics_nonterminalCount
    [DecidableEq Terminal] (grammar : PegGrammar Terminal nonterminalCount) :
    grammar.sizeStatistics.nonterminalCount = nonterminalCount :=
  rfl

@[simp] theorem sizeStatistics_coreNodeCount
    [DecidableEq Terminal] (grammar : PegGrammar Terminal nonterminalCount) :
    grammar.sizeStatistics.coreNodeCount = grammar.coreNodeCount :=
  rfl

@[simp] theorem sizeStatistics_hashConsedCoreNodeCount
    [DecidableEq Terminal] (grammar : PegGrammar Terminal nonterminalCount) :
    grammar.sizeStatistics.hashConsedCoreNodeCount =
      grammar.hashConsedCoreNodeCount :=
  rfl

theorem coreNodeCount_eq_sum
    (grammar : PegGrammar Terminal nonterminalCount) :
    grammar.coreNodeCount =
      ∑ name : Fin nonterminalCount,
        (grammar.rule name).coreNodeCount :=
  rfl

end PegGrammar

end PegSeparation
