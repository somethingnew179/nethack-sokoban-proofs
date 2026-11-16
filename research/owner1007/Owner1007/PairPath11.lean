import Owner1007.PairPath11ChecksA
import Owner1007.PairPath11ChecksB
import Owner1007.PairPath11ChecksC
namespace Owner1007.PairPath11
open NetHack.Sokoban
theorem checked : PricedCorral11.checkExcept soko1_1.board soko1_1.initial.holes locks region paid = true := by
  change (List.finRange 9).all nodeCheck = true
  apply List.all_eq_true.mpr
  intro i _
  obtain ⟨i,bound⟩ := i
  have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact node0
  · exact node1
  · exact node2
  · exact node3
  · exact node4
  · exact node5
  · exact node6
  · exact node7
  · exact node8

theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
  PricedCorral11.closed_of_checkExcept _ _ _ _ _ checked
#print axioms closed
#print axioms initial_good
end Owner1007.PairPath11
