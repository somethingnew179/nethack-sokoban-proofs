import Owner1007.RightCapacity12Upper0
import Owner1007.RightCapacity12Upper1
import Owner1007.RightCapacity12Upper2
import Owner1007.RightCapacity12Upper3
import Owner1007.RightCapacity12Upper4
import Owner1007.RightCapacity12Low0
import Owner1007.RightCapacity12Low1
import Owner1007.RightCapacity12Low2
import Owner1007.RightCapacity12Low3
import Owner1007.RightCapacity12Low4
import Owner1007.RightCapacity12Token0
import Owner1007.RightCapacity12Token1
namespace Owner1007.RightCapacity12
open NetHack.Sokoban
theorem upperMatrix : PricedCorral.check soko1_2.board soko1_2.initial.holes p upperLocks upperRegion upperCredit = true := by
  change (List.finRange 5).all upperNode = true
  apply List.all_eq_true.mpr
  intro i _
  obtain ⟨i,bound⟩ := i
  have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl
  · exact upperNode0
  · exact upperNode1
  · exact upperNode2
  · exact upperNode3
  · exact upperNode4
theorem lowMatrix : PricedCorral.check soko1_2.board soko1_2.initial.holes p lowLocks lowRegion lowCredit = true := by
  change (List.finRange 5).all lowNode = true
  apply List.all_eq_true.mpr
  intro i _
  obtain ⟨i,bound⟩ := i
  have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl
  · exact lowNode0
  · exact lowNode1
  · exact lowNode2
  · exact lowNode3
  · exact lowNode4
theorem tokenMatrix : PricedCorral.check soko1_2.board soko1_2.initial.holes p tokenLocks tokenRegion tokenCredit = true := by
  change (List.finRange 2).all tokenNode = true
  apply List.all_eq_true.mpr
  intro i _
  obtain ⟨i,bound⟩ := i
  have choices : i=0 ∨ i=1 := by omega
  rcases choices with rfl | rfl
  · exact tokenNode0
  · exact tokenNode1
#print axioms upperMatrix
#print axioms lowMatrix
#print axioms tokenMatrix
end Owner1007.RightCapacity12
