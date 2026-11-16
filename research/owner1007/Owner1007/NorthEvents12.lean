import Owner1007.NorthEvents12Node0
import Owner1007.NorthEvents12Node1
import Owner1007.NorthEvents12Node2
import Owner1007.NorthEvents12Node3
import Owner1007.NorthEvents12Node4
namespace Owner1007.NorthEvents12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open Owner1007
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid = true := by
  change (List.finRange 5).all nodeCheck = true
  apply List.all_eq_true.mpr
  intro i _
  obtain ⟨i,bound⟩ := i
  have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl
  · exact node0
  · exact node1
  · exact node2
  · exact node3
  · exact node4
theorem j_guard_check : ∀ i, GuardNode i := by
  intro i
  obtain ⟨i,bound⟩ := i
  have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl
  · exact guard0
  · exact guard1
  · exact guard2
  · exact guard3
  · exact guard4
theorem j_guard : ∀ i hero, hero ∈ region i → ∀ dir source, source ∈ J →
    advance soko1_2.board hero dir = some source →
      BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir := by
  intro i hero heroInside dir source member adjacent
  exact j_guard_check i hero heroInside dir (Geometry.all_directions dir) source member adjacent

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

theorem north_contains_paid {dirs final pushes moves}
    (trace : Trace soko1_2.board FirstSplit12.afterN dirs final pushes moves)
    (completed : Goal final) :
    PricedCorral11.PaidTrace soko1_2.board paid FirstSplit12.afterN dirs final pushes moves := by
  have conserved := trace.conservation
  have empty : final.holes=[] := completed
  change 20 + final.holes.length = final.boulders.length + 18 at conserved
  rw [empty] at conserved
  simp only [List.length_nil] at conserved
  exact completing_contains_paid trace ⟨0,by decide +kernel,by decide +kernel⟩
    (by intro c h; exact h) (by omega)
#print axioms north_contains_paid
#print axioms j_guard
#print axioms paid_cost
end Owner1007.NorthEvents12
