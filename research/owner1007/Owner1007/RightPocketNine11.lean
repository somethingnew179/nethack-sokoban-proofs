import Owner1007.RightPocketDead11
import Owner1007.Budget32711
namespace Owner1007.RightPocketNine11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperBudget11
/-- Current physical ownership suffices; no original191 stationarity. -/
theorem reserve_nine {state final : State}
 {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (hero : state.player∈RightPocketDead11.region 0)
 (selected : RightPocketDead11.locks 0⊆endGroup U6 before) :
 9≤energy soko1_1.initial final U6 (before++outcomes) := by
 by_cases enough : 9≤energy soko1_1.initial final U6 (before++outcomes)
 · exact enough
 · have cap : energy soko1_1.initial final U6 (before++outcomes)≤8 := by omega
   have gone := Budget32711.upper_gone (first.append last) completed cap
   have suffixGone : endGroup (endGroup U6 before) outcomes=[] := by rw [←endGroup_append];exact gone
   have facts := first.end_subset (by decide) U6 (by decide) (by decide)
   have bounded := endGroup_length_le U6 before
   change (endGroup U6 before).length≤6 at bounded
   exact False.elim (RightPocketDead11.impossible_gone first.trace last (endGroup U6 before)
     facts.1 facts.2 (by omega) hero selected suffixGone)
#print axioms reserve_nine
end Owner1007.RightPocketNine11
