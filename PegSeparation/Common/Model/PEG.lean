import Mathlib


namespace PegSeparation

inductive ParsingExpression (Terminal : Type) (nonterminalCount : Nat) where
  | empty
  | failure
  | terminal (symbol : Terminal)
  | nonterminal (name : Fin nonterminalCount)
  | sequence (left right : ParsingExpression Terminal nonterminalCount)
  | orderedChoice (left right : ParsingExpression Terminal nonterminalCount)
  | notPredicate (body : ParsingExpression Terminal nonterminalCount)
  | andPredicate (body : ParsingExpression Terminal nonterminalCount)

structure PegGrammar (Terminal : Type) (nonterminalCount : Nat) where
  rule : Fin nonterminalCount → ParsingExpression Terminal nonterminalCount
  start : Fin nonterminalCount

inductive ParseResult (Terminal : Type) where
  | failure
  | success (remaining : List Terminal)
  deriving Repr

namespace PegGrammar

variable {Terminal : Type} {nonterminalCount : Nat}

def terminalResult [DecidableEq Terminal] (wanted : Terminal) :
    List Terminal → ParseResult Terminal
  | [] => .failure
  | actual :: rest => if actual = wanted then .success rest else .failure

inductive Evaluates [DecidableEq Terminal]
    (grammar : PegGrammar Terminal nonterminalCount) :
    ParsingExpression Terminal nonterminalCount →
      List Terminal → ParseResult Terminal → Prop where
  | empty (input) : Evaluates grammar .empty input (.success input)
  | failure (input) : Evaluates grammar .failure input .failure
  | terminal (symbol input) :
      Evaluates grammar (.terminal symbol) input (terminalResult symbol input)
  | nonterminal {name input result}
      (body : Evaluates grammar (grammar.rule name) input result) :
      Evaluates grammar (.nonterminal name) input result
  | sequenceFailure {left right input}
      (leftFails : Evaluates grammar left input .failure) :
      Evaluates grammar (.sequence left right) input .failure
  | sequenceSuccess {left right input middle result}
      (leftSucceeds : Evaluates grammar left input (.success middle))
      (rightResult : Evaluates grammar right middle result) :
      Evaluates grammar (.sequence left right) input result
  | choiceLeft {left right input remaining}
      (leftSucceeds : Evaluates grammar left input (.success remaining)) :
      Evaluates grammar (.orderedChoice left right) input (.success remaining)
  | choiceRight {left right input result}
      (leftFails : Evaluates grammar left input .failure)
      (rightResult : Evaluates grammar right input result) :
      Evaluates grammar (.orderedChoice left right) input result
  | notSuccess {body input}
      (bodyFails : Evaluates grammar body input .failure) :
      Evaluates grammar (.notPredicate body) input (.success input)
  | notFailure {body input remaining}
      (bodySucceeds : Evaluates grammar body input (.success remaining)) :
      Evaluates grammar (.notPredicate body) input .failure
  | andSuccess {body input remaining}
      (bodySucceeds : Evaluates grammar body input (.success remaining)) :
      Evaluates grammar (.andPredicate body) input (.success input)
  | andFailure {body input}
      (bodyFails : Evaluates grammar body input .failure) :
      Evaluates grammar (.andPredicate body) input .failure

def IsLoffTotal [DecidableEq Terminal]
    (grammar : PegGrammar Terminal nonterminalCount) : Prop :=
  ∀ (expression : ParsingExpression Terminal nonterminalCount) (input : List Terminal),
    ∃ result, Evaluates grammar expression input result

def Recognizes [DecidableEq Terminal]
    (grammar : PegGrammar Terminal nonterminalCount) (input : List Terminal) : Prop :=
  Evaluates grammar (.nonterminal grammar.start) input (.success [])

end PegGrammar

end PegSeparation
