import Owner1007.RestLeft212Ticket11
import Owner1007.TightRowPairs32711
import Owner1007.Zero186Cycle32711
import Owner1007.LeftSameActor11
namespace Owner1007.ModeLeftSix32711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ticket {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327) :
 2≤energy soko1_1.initial final Rest outcomes+energy soko1_1.initial final [212] outcomes := by
 have capacity : ¬([187,212] : List Cell)⊆final.boulders := by
  intro physical
  have bound := TightRowPairs32711.other_capacity logged completed cheap [187,212] (by decide) physical (by decide)
  change 2≤1 at bound
  omega
 exact RestLeft212Ticket11.sum_at_least_two_capacity logged completed (by omega) capacity

theorem left_split {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327)
 (upper : energy soko1_1.initial final U6 outcomes=6)
 (left : energy soko1_1.initial final TightSplit11.B outcomes=6)
 (rest : energy soko1_1.initial final Rest outcomes=0) :
 (energy soko1_1.initial final [186] outcomes=2 ∧energy soko1_1.initial final [212] outcomes=4) ∨
 (energy soko1_1.initial final [186] outcomes=4 ∧energy soko1_1.initial final [212] outcomes=2) := by
 have ticket := ticket logged completed cheap
 have pair := Hero315Frame11.energy_split logged [186] [212] (by decide) (by decide)
 change energy soko1_1.initial final TightSplit11.B outcomes=
   energy soko1_1.initial final [186] outcomes+energy soko1_1.initial final [212] outcomes at pair
 have nn186 := energy_nonnegative logged [186] (by decide) (by decide)
 have nonzero186 : energy soko1_1.initial final [186] outcomes≠0 := by
  intro zero
  exact Zero186Cycle32711.impossible logged completed cheap (by omega) (by omega) zero
 have gone186 := TightSurvivors11.singleton_nil logged completed TightSplit11.B (by decide) (by decide) (by decide) 6 (by omega)
   186 (by decide) (by decide +kernel)
 have gone212 := TightSurvivors11.singleton_nil logged completed TightSplit11.B (by decide) (by decide) (by decide) 6 (by omega)
   212 (by decide) (by decide +kernel)
 have even186 := ConsumedParity11.consumed_even logged completed [186] (by decide) (by decide) gone186
 have even212 := ConsumedParity11.consumed_even logged completed [212] (by decide) (by decide) gone212
 omega

theorem modeA_zero186 {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327)
 (left : energy soko1_1.initial final TightSplit11.B outcomes=4)
 (rest : energy soko1_1.initial final Rest outcomes=0) :
 energy soko1_1.initial final [186] outcomes=0 := by
 have ticket := ticket logged completed cheap
 have gone := Budget32711.left_gone logged completed (by omega)
 have pairCheap : energy soko1_1.initial final [186,212] outcomes≤4 := by
  change energy soko1_1.initial final TightSplit11.B outcomes≤4
  omega
 have counts := LeftSameActor11.count_two_one_actor logged completed pairCheap gone
 have actorFour : 4≤energy soko1_1.initial final [186] outcomes ∨4≤energy soko1_1.initial final [212] outcomes := by
  rcases counts with first|second
  ·exact Or.inl (LeftActorCount11.actor_four logged 186 (by decide) first)
  ·exact Or.inr (LeftActorCount11.actor_four logged 212 (by decide) second)
 have pair := Hero315Frame11.energy_split logged [186] [212] (by decide) (by decide)
 change energy soko1_1.initial final TightSplit11.B outcomes=
   energy soko1_1.initial final [186] outcomes+energy soko1_1.initial final [212] outcomes at pair
 have nn186 := energy_nonnegative logged [186] (by decide) (by decide)
 rcases actorFour with first|second <;> omega
#print axioms ticket
#print axioms left_split
#print axioms modeA_zero186
end Owner1007.ModeLeftSix32711
