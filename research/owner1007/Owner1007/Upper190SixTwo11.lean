import Owner1007.Q190Upper11Helpers
import Owner1007.UpperBudget11
namespace Owner1007.Upper190SixTwo11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem upper_eight {state final : State} {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (prefixSix : 6≤energy soko1_1.initial state UpperBudget11.U6 before)
 (selected : [137,139,190]⊆endGroup UpperBudget11.U6 before)
 (hero : state.player∈UpperZero11.region 12) :
 8≤energy soko1_1.initial final UpperBudget11.U6 (before++outcomes) := by
 have facts:=first.end_subset (by decide) UpperBudget11.U6 (by decide) (by decide)
 have size : (endGroup UpperBudget11.U6 before).length≤18:=by
  have bound:=endGroup_length_le UpperBudget11.U6 before
  have six : UpperBudget11.U6.length=6:=rfl
  rw [six] at bound
  omega
 have future:=Q190Upper11.zero_future_two first.trace logged completed
  (endGroup UpperBudget11.U6 before) facts.1 facts.2 size 12 selected hero
 have split:=energy_append soko1_1.initial state final UpperBudget11.U6 before outcomes
 omega
#print axioms upper_eight
end Owner1007.Upper190SixTwo11
