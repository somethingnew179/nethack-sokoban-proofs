import Owner1007.Budget32711
import Owner1007.Upper216Eight11
namespace Owner1007.UpperNoFrozen11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperBudget11
/-- A frozen nonempty current subset cannot belong to the original Upper
group when its whole completing energy is at most eight. -/
theorem excluded {state final : State}
 {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (cap : energy soko1_1.initial final U6 (before++outcomes)≤8)
 (frozen : List Cell) (locked : Locked soko1_1.board frozen) (cell : Cell) (member : cell∈frozen)
 (selected : frozen⊆endGroup U6 before) : False := by
 have gone := Budget32711.upper_gone (first.append last) completed cap
 have suffixGone : endGroup (endGroup U6 before) outcomes=[] := by rw [←endGroup_append];exact gone
 have facts := first.end_subset (by decide) U6 (by decide) (by decide)
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 exact Upper216Eight11.frozen_absurd last valid.1 facts.1 facts.2 locked
   (List.Subset.trans selected facts.2) member (selected member) suffixGone
#print axioms excluded
end Owner1007.UpperNoFrozen11
