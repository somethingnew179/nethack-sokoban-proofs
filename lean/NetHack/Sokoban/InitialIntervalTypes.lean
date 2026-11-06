/- Small shared interface for original-map interval claims. Compiling these
definitions separately avoids rebuilding their environment in the combined
certificate registry. The original names and propositions are preserved. -/
import NetHack.Sokoban.Maps
namespace NetHack.Sokoban.InitialIntervals

structure PushInterval (level : SourceMap) (lower upper : Nat) : Prop where
  lower_bound : ∀ directions final pushes moves,
    Trace level.board level.initial directions final pushes moves → Goal final → lower ≤ pushes
  upper_bound : ∃ directions final moves,
    Trace level.board level.initial directions final upper moves ∧ Goal final

/-- Exact equivalence with the previous conjunction interface; no change
in states, legal traces, completion condition or costs. -/
theorem pushInterval_iff (level : SourceMap) (lower upper : Nat) :
    PushInterval level lower upper ↔
      ((∀ directions final pushes moves,
        Trace level.board level.initial directions final pushes moves → Goal final → lower ≤ pushes) ∧
       ∃ directions final moves,
        Trace level.board level.initial directions final upper moves ∧ Goal final) :=
  ⟨fun checked => ⟨checked.lower_bound,checked.upper_bound⟩,fun checked => ⟨checked.1,checked.2⟩⟩

def lowerTable : List Nat := [321,220,109,87,136,140,80,85]
def upperTable : List Nat := [375,235,109,87,136,147,80,85]

/-- Exact interval claim for the indexed complete canonical source map. -/
def Claim (index : Fin 8) : Prop :=
  PushInterval (sourceMaps[index.val]'(index.isLt))
    (lowerTable[index.val]'(index.isLt)) (upperTable[index.val]'(index.isLt))

end NetHack.Sokoban.InitialIntervals
