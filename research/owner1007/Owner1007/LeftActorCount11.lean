import Owner1007.LeftQuietIdentity11
namespace Owner1007.LeftActorCount11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem actor_four {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (cell : Cell) (member : cell∈soko1_1.initial.boulders)
 (twice : 2≤PaidCount11.count LeftPair11.paid [cell] dirs outcomes) :
 4≤energy soko1_1.initial final [cell] outcomes := by
 have bound := PaidCount11.energy_bound LeftSplit11.priced logged
   NetHack.SokobanLinearPhases.Map11.initial_good [cell] (by simp) (by simpa using member) (by simp)
 simp only [Int.ofNat_eq_natCast] at bound
 omega
#print axioms actor_four
end Owner1007.LeftActorCount11
