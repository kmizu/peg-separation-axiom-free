import PegSeparation.CFLNotPEG.Witness.LanguageCFG
import PegSeparation.Common.Model.PEGRender
import PegSeparation.Common.Model.PEGSize


namespace PegSeparation.Witness.DirectPEG

open PegSeparation

abbrev Terminal := LanguageCFG.Terminal
abbrev Word := LanguageCFG.Word
abbrev Expr := ParsingExpression Terminal 10


def bitName : Fin 10 := ⟨0, by omega⟩
def bitsName : Fin 10 := ⟨1, by omega⟩
def entryName : Fin 10 := ⟨2, by omega⟩
def restName : Fin 10 := ⟨3, by omega⟩
def m0Name : Fin 10 := ⟨4, by omega⟩
def m1Name : Fin 10 := ⟨5, by omega⟩
def keyName : Fin 10 := ⟨6, by omega⟩
def endName : Fin 10 := ⟨7, by omega⟩
def hitName : Fin 10 := ⟨8, by omega⟩
def searchName : Fin 10 := ⟨9, by omega⟩

private def tm (symbol : Terminal) : Expr :=
  .terminal symbol

private def nt (name : Fin 10) : Expr :=
  .nonterminal name

private def seq3 (first second third : Expr) : Expr :=
  .sequence first (.sequence second third)

private def seq5 (first second third fourth fifth : Expr) : Expr :=
  .sequence first
    (.sequence second (.sequence third (.sequence fourth fifth)))

private def choice3 (first second third : Expr) : Expr :=
  .orderedChoice first (.orderedChoice second third)


def bitRule : Expr :=
  .orderedChoice (tm .bit0) (tm .bit1)

def bitsRule : Expr :=
  .orderedChoice
    (.sequence (nt bitName) (nt bitsName))
    (nt bitName)

def entryRule : Expr :=
  seq5 (tm .langle) (nt bitsName) (tm .colon)
    (nt bitsName) (tm .rangle)

def restRule : Expr :=
  .orderedChoice
    (.sequence (nt entryName) (nt restName))
    .empty

def m0Rule : Expr :=
  choice3
    (seq3 (tm .bit0) (nt m0Name) (nt bitName))
    (.sequence (tm .bit1)
      (.orderedChoice
        (.sequence (nt m0Name) (tm .bit0))
        (.sequence (nt m1Name) (tm .bit1))))
    (seq3 (tm .rangle) (nt restName) (tm .dollar))

def m1Rule : Expr :=
  .orderedChoice
    (seq3 (tm .bit0) (nt m1Name) (nt bitName))
    (.sequence (tm .bit1)
      (.orderedChoice
        (.sequence (nt m1Name) (tm .bit0))
        (.sequence (nt m0Name) (tm .bit1))))

def keyRule : Expr :=
  choice3
    (seq3 (tm .bit0) (nt keyName) (tm .bit0))
    (seq3 (tm .bit1) (nt keyName) (tm .bit1))
    (seq3 (tm .colon) (nt m1Name) (tm .hash))

def anyTerminal : Expr :=
  .orderedChoice (tm .bit0)
    (.orderedChoice (tm .bit1)
      (.orderedChoice (tm .langle)
        (.orderedChoice (tm .colon)
          (.orderedChoice (tm .rangle)
            (.orderedChoice (tm .dollar) (tm .hash))))))

def endRule : Expr :=
  .notPredicate anyTerminal

def hitRule : Expr :=
  seq3 (tm .langle)
    (.orderedChoice
      (seq3 (tm .bit0) (nt keyName) (tm .bit0))
      (seq3 (tm .bit1) (nt keyName) (tm .bit1)))
    (nt endName)

def searchRule : Expr :=
  .orderedChoice
    (nt hitName)
    (.sequence (nt entryName) (nt searchName))

def grammar : PegGrammar Terminal 10 where
  rule name :=
    match name.val with
    | 0 => bitRule
    | 1 => bitsRule
    | 2 => entryRule
    | 3 => restRule
    | 4 => m0Rule
    | 5 => m1Rule
    | 6 => keyRule
    | 7 => endRule
    | 8 => hitRule
    | _ => searchRule
  start := searchName

@[simp] theorem grammar_rule_bit :
    grammar.rule bitName = bitRule := rfl

@[simp] theorem grammar_rule_bits :
    grammar.rule bitsName = bitsRule := rfl

@[simp] theorem grammar_rule_entry :
    grammar.rule entryName = entryRule := rfl

@[simp] theorem grammar_rule_rest :
    grammar.rule restName = restRule := rfl

@[simp] theorem grammar_rule_m0 :
    grammar.rule m0Name = m0Rule := rfl

@[simp] theorem grammar_rule_m1 :
    grammar.rule m1Name = m1Rule := rfl

@[simp] theorem grammar_rule_key :
    grammar.rule keyName = keyRule := rfl

@[simp] theorem grammar_rule_end :
    grammar.rule endName = endRule := rfl

@[simp] theorem grammar_rule_hit :
    grammar.rule hitName = hitRule := rfl

@[simp] theorem grammar_rule_search :
    grammar.rule searchName = searchRule := rfl

@[simp] theorem grammar_start :
    grammar.start = searchName := rfl


def renderTerminal : Terminal → String
  | .bit0 => "0"
  | .bit1 => "1"
  | .langle => "langle"
  | .colon => "colon"
  | .rangle => "rangle"
  | .dollar => "dollar"
  | .hash => "hash"

def renderedGrammar : String :=
  PEGRender.renderGrammar renderTerminal grammar

def grammarStatistics : PegSizeStatistics :=
  grammar.sizeStatistics

set_option maxRecDepth 10000 in
theorem grammarStatistics_eq :
    grammarStatistics =
      { nonterminalCount := 10
        coreNodeCount := 109
        hashConsedCoreNodeCount := 64 } := by
  decide

end PegSeparation.Witness.DirectPEG
