import Owner1007.Corral11

namespace Owner1007.ShaftCorral11
open NetHack.Sokoban

def locks (_ : Fin 1) : List Cell := [190,191,216]
def region (_ : Fin 1) : List Cell :=
  Corral11.regionBase.filter fun c =>
    !([190,191,192,193,194,215,216,217,218,219,220] : List Cell).contains c

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked : Corral11.check soko1_1.board soko1_1.initial.holes locks region = true := by
  decide +kernel
theorem closed : Corral11.Closed soko1_1.board soko1_1.initial.holes locks region :=
  Corral11.closed_of_check _ _ _ _ checked
theorem unique (i : Fin 1) : (locks i).Nodup := by
  change ([190,191,216] : List Cell).Nodup
  decide +kernel

/-- The shaft cut preserves three stones, whereas a completed original board has two. -/
theorem excluded {state final : State} {history dirs : List Dir}
    {previousPushes previousMoves pushes moves : Nat}
    (reached : Trace soko1_1.board soko1_1.initial history state previousPushes previousMoves)
    (tail : Trace soko1_1.board state dirs final pushes moves) (completed : Goal final) :
    ¬ Corral11.Good locks region state := by
  intro good
  have holesInside : state.holes ⊆ soko1_1.initial.holes := reached.holes_sublist.subset
  obtain ⟨i, _, persists⟩ := Corral11.trace_good closed unique tail good holesInside
  have cardinality := List.Nodup.length_le_of_subset (unique i) persists
  have prefixConserved := reached.conservation
  have suffixConserved := tail.conservation
  have empty : final.holes = [] := completed
  change 18 + state.holes.length = state.boulders.length + 16 at prefixConserved
  rw [empty] at suffixConserved
  change 3 ≤ final.boulders.length at cardinality
  simp only [List.length_nil] at suffixConserved
  omega

#print axioms excluded
end Owner1007.ShaftCorral11
