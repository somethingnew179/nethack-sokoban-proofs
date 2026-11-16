import Owner1007.FirstSplit12
import NetHack.Sokoban.Generated.Soko12Potential
namespace Owner1007.After26512
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def current : Fin 4 → Cell | 0 => 345 | 1 => 319 | 2 => 293 | 3 => 292
def locks (i : Fin 4) : List Cell := [291,318,current i]
def sealed : Fin 4 → List Cell
 | 0 => [317,319,320,292,293,294]
 | 1 => [317,320,292,293,294]
 | 2 => [317,292]
 | 3 => [317]
def region (i : Fin 4) : List Cell :=
 soko1_2.board.floor.filter fun c => !(locks i).contains c && !(sealed i).contains c
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=291 ∧ (dir=.east ∨ dir=.west ∨ dir=.south)) ∨ (source=318 ∧ dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid = true := by decide +kernel
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem size : ∀ i, (locks i).length=3 := by decide +kernel
theorem start_hero : ∀ i, 265 ∈ region i := by decide +kernel
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
def fixed : List Cell := [291,318]
theorem fixed_inside : ∀ i, fixed ⊆ locks i := by decide +kernel
theorem fixed_guard_check : ∀ i, ∀ hero ∈ region i, ∀ dir ∈ allDirs, ∀ source ∈ fixed,
    advance soko1_2.board hero dir = some source →
      BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir := by decide +kernel
theorem fixed_guard : ∀ i hero, hero ∈ region i → ∀ dir source, source ∈ fixed →
    advance soko1_2.board hero dir = some source →
      BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir := by
  intro i hero heroInside dir source member adjacent
  exact fixed_guard_check i hero heroInside dir (Geometry.all_directions dir) source member adjacent
theorem paid_cost : ∀ source ∈ [291,318], ∀ dir ∈ allDirs,
 paid source dir → ∀ dest ∈ pushTargets soko1_2.board source dir,
 dest ∉ soko1_2.initial.holes ∧
 1 + Generated.soko1_2Potential.boulder dest - Generated.soko1_2Potential.boulder source =
 (if source=318 then 3 else if dir=.south then 7 else 2) := by decide +kernel
#print axioms completing_contains_paid
#print axioms fixed_guard
#print axioms paid_cost
end Owner1007.After26512
