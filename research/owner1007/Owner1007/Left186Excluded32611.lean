import Owner1007.Left186Excluded326Core11
import Owner1007.TightRowPairs32611
namespace Owner1007.Left186Excluded32611
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem not_four {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤326)
 (four186 : 4≤energy soko1_1.initial final [186] outcomes) : False := by
 apply not_four_capacity logged completed cheap four186
 intro inside
 have bound := TightRowPairs32611.other_capacity logged completed cheap [187,212] (by decide) inside (by decide)
 change 2≤1 at bound
 omega

theorem only_second_actor {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤326) :
 4≤energy soko1_1.initial final [212] outcomes := by
 have left := (Tight32611.budgets logged completed cheap).2.2.1
 change energy soko1_1.initial final [186,212] outcomes=4 at left
 have gone : endGroup [186,212] outcomes=[] := by
   apply TightSurvivors11.all_nil logged (by decide) [186,212] (by decide) (by decide)
   intro cell member
   apply TightSurvivors11.singleton_nil logged completed [186,212] (by decide) (by decide) (by decide) 4 (by omega) cell member
   have check : ([186,212] : List Cell).all (fun c=>decide (value soko1_1.initial [c]< -4))=true := by decide +kernel
   exact of_decide_eq_true (List.all_eq_true.mp check cell member)
 rcases LeftSameActor11.count_two_one_actor logged completed (by omega) gone with first|second
 ·exact False.elim (not_four logged completed cheap (LeftActorCount11.actor_four logged 186 (by decide) first))
 ·exact LeftActorCount11.actor_four logged 212 (by decide) second
#print axioms not_four
#print axioms only_second_actor
end Owner1007.Left186Excluded32611
