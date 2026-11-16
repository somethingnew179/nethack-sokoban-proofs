import Owner1007.FirstSplit12
import NetHack.Sokoban.Generated.Soko12Potential

namespace Owner1007.RingCut12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.LowerBounds
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def locks (_ : Fin 1) : List Cell := [210,237,263,290]
def outside : List Cell := [236,262,288,289]
def region (_ : Fin 1) : List Cell :=
 soko1_2.board.floor.filter fun c => !outside.contains c && !([210,237,263,290] : List Cell).contains c
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=210 ∧ dir=.south) ∨ (source=237 ∧ dir=.west) ∨
 (source=263 ∧ dir=.west) ∨ (source=290 ∧ dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid = true := by decide +kernel
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem size : ∀ i, (locks i).length=4 := by decide +kernel

theorem completing_contains_paid {state final dirs pushes moves}
    (trace : Trace soko1_2.board state dirs final pushes moves)
    (good : Corral11.Good locks region state)
    (holes : state.holes ⊆ soko1_2.initial.holes)
    (count : final.boulders.length ≤ 2) :
    PricedCorral11.PaidTrace soko1_2.board paid state dirs final pushes moves := by
  have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
  rcases PricedCorral11.event_or_good closed unique trace good holes with found | terminal
  · exact found
  · obtain ⟨i,hero,inside⟩ := terminal
    have small := List.Nodup.length_le_of_subset (unique i) inside
    have large := size i
    omega

abbrev p := Generated.soko1_2Potential
theorem paid_cost : ∀ source ∈ [210,237,263,290], ∀ dir ∈ allDirs,
    paid source dir → ∀ dest ∈ pushTargets soko1_2.board source dir,
    dest ∉ soko1_2.initial.holes ∧ 1 + p.boulder dest - p.boulder source = 2 := by decide +kernel
#print axioms completing_contains_paid
#print axioms paid_cost
end Owner1007.RingCut12
