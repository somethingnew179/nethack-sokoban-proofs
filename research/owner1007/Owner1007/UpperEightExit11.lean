import Owner1007.UpperEightBudget11
import Owner1007.StationaryExitSix11
namespace Owner1007.UpperEightExit11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11 Owner1007.UpperCutBudget11
theorem survivor_eight_absurd {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cheap : energy soko1_1.initial final U6 outcomes<8) (cell : Cell) (member : cell∈[139,191])
 (survives : endGroup [cell] outcomes≠[]) : False := by
 have subset : [cell]⊆U6 := by
   rcases List.mem_cons.mp member with rfl|later
   · decide
   · have same : cell=191 := List.mem_singleton.mp later
     subst cell; decide
 have bound := energy_subset (Trace.nil soko1_1.initial) logged [cell] U6 (by simp) (by decide)
   subset (by decide) (by decide)
 have ledger := survivor_energy logged completed cell survives
 have debt : value soko1_1.initial [cell]≤-8 := by
   rcases List.mem_cons.mp member with rfl|later
   · decide +kernel
   · have same : cell=191 := List.mem_singleton.mp later
     subst cell; decide +kernel
 have nonnegative : (0:Int)≤Int.ofNat (ownPushes [cell] outcomes) := Int.ofNat_nonneg _
 omega

#print axioms survivor_eight_absurd
end Owner1007.UpperEightExit11
