import Owner1007.PricedCorral11
import NetHack.Soko11Hero315.Reader

namespace Owner1007.QueuedCorral11
open NetHack.Sokoban

def locks (_ : Fin 1) : List Cell := [112,137,139]
def region (_ : Fin 1) : List Cell :=
  (NetHack.SokobanLinearPhases.Map11.heroesRegion0.filter fun c => decide (183 ≤ c)) ++ [164,138]
def paid (source : Cell) (dir : Dir) : Prop :=
  (source = 137 ∧ dir = .west) ∨ (source = 139 ∧ dir = .east)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by
  unfold paid
  infer_instance

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked : PricedCorral11.checkExcept soko1_1.board soko1_1.initial.holes locks region paid = true := by
  decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
  PricedCorral11.closed_of_checkExcept _ _ _ _ _ checked
theorem unique (i : Fin 1) : (locks i).Nodup := by
  change ([112,137,139] : List Cell).Nodup
  decide +kernel

/-- A queued stone at112 cannot complete without one of the two gate exits. -/
theorem completing_contains_paid {state final : State} {history dirs : List Dir}
    {previousPushes previousMoves pushes moves : Nat}
    (reached : Trace soko1_1.board soko1_1.initial history state previousPushes previousMoves)
    (tail : Trace soko1_1.board state dirs final pushes moves) (completed : Goal final)
    (good : Corral11.Good locks region state) :
    PricedCorral11.PaidTrace soko1_1.board paid state dirs final pushes moves := by
  have holesInside : state.holes ⊆ soko1_1.initial.holes := reached.holes_sublist.subset
  rcases PricedCorral11.event_or_good closed unique tail good holesInside with found | finalGood
  · exact found
  · obtain ⟨i, _, persists⟩ := finalGood
    have cardinality := List.Nodup.length_le_of_subset (unique i) persists
    have prefixConserved := reached.conservation
    have suffixConserved := tail.conservation
    have empty : final.holes = [] := completed
    change 18 + state.holes.length = state.boulders.length + 16 at prefixConserved
    rw [empty] at suffixConserved
    change 3 ≤ final.boulders.length at cardinality
    simp only [List.length_nil] at suffixConserved
    omega

#print axioms completing_contains_paid
end Owner1007.QueuedCorral11
