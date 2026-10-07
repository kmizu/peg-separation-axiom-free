import PegSeparation.Common.Model.PEG


namespace PegSeparation

namespace PEGRender

variable {Terminal : Type} {nonterminalCount : Nat}

def renderNonterminal (name : Fin nonterminalCount) : String :=
  "N" ++ toString name.val

def renderExpression (renderTerminal : Terminal → String) :
    ParsingExpression Terminal nonterminalCount → String
  | .empty =>
      "(empty)"
  | .failure =>
      "(failure)"
  | .terminal symbol =>
      "(terminal " ++ renderTerminal symbol ++ ")"
  | .nonterminal name =>
      "(nonterminal " ++ renderNonterminal name ++ ")"
  | .sequence left right =>
      "(sequence " ++
        renderExpression renderTerminal left ++ " " ++
        renderExpression renderTerminal right ++ ")"
  | .orderedChoice left right =>
      "(choice " ++
        renderExpression renderTerminal left ++ " " ++
        renderExpression renderTerminal right ++ ")"
  | .notPredicate body =>
      "(not " ++ renderExpression renderTerminal body ++ ")"
  | .andPredicate body =>
      "(and " ++ renderExpression renderTerminal body ++ ")"

def renderRule
    (renderTerminal : Terminal → String)
    (grammar : PegGrammar Terminal nonterminalCount)
    (name : Fin nonterminalCount) : String :=
  "(rule " ++ renderNonterminal name ++ " " ++
    renderExpression renderTerminal (grammar.rule name) ++ ")"

def numberedRules
    (renderTerminal : Terminal → String)
    (grammar : PegGrammar Terminal nonterminalCount) : List String :=
  (List.finRange nonterminalCount).map (renderRule renderTerminal grammar)

@[simp]
theorem numberedRules_length
    (renderTerminal : Terminal → String)
    (grammar : PegGrammar Terminal nonterminalCount) :
    (numberedRules renderTerminal grammar).length = nonterminalCount := by
  simp [numberedRules]

def renderGrammar
    (renderTerminal : Terminal → String)
    (grammar : PegGrammar Terminal nonterminalCount) : String :=
  String.intercalate "\n"
      (["(peg", "  (start " ++ renderNonterminal grammar.start ++ ")"] ++
        (numberedRules renderTerminal grammar).map ("  " ++ ·) ++
        [")"]) ++
    "\n"

end PEGRender

end PegSeparation
