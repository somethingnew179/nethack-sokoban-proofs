import Owner1007.Tight32611
import Owner1007.LeftSameActor11
namespace Owner1007.LeftSameActor32611
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11

theorem canonical_count_two {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤326) :
 2≤PaidCount11.count LeftPair11.paid [186] dirs outcomes ∨
 2≤PaidCount11.count LeftPair11.paid [212] dirs outcomes := by
 have left := (Tight32611.budgets logged completed cheap).2.2.1
 change energy soko1_1.initial final [186,212] outcomes=4 at left
 have gone : endGroup [186,212] outcomes=[] := by
  apply TightSurvivors11.all_nil logged (by decide) [186,212] (by decide) (by decide)
  intro cell member
  apply TightSurvivors11.singleton_nil logged completed [186,212] (by decide) (by decide) (by decide) 4 (by omega) cell member
  have debts : ([186,212] : List Cell).all (fun c=>decide (value soko1_1.initial [c]< -4))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp debts cell member)
 exact LeftSameActor11.count_two_one_actor logged completed (by omega) gone

theorem canonical_actor_four {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤326) :
 4≤energy soko1_1.initial final [186] outcomes ∨4≤energy soko1_1.initial final [212] outcomes := by
 rcases canonical_count_two logged completed cheap with first|second
 ·exact Or.inl (LeftActorCount11.actor_four logged 186 (by decide) first)
 ·exact Or.inr (LeftActorCount11.actor_four logged 212 (by decide) second)
#print axioms canonical_count_two
#print axioms canonical_actor_four
end Owner1007.LeftSameActor32611
