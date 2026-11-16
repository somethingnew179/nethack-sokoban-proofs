import Owner1007.ZeroRestTail11
namespace Owner1007.RestTailBudget11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem subset_le {beforeDirs state beforePushes beforeMoves before afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state afterDirs final afterPushes afterMoves after)
 (group : List Cell) (groupUnique : group.Nodup) (subset : group⊆endGroup UpperBudget11.Rest before) :
 energy state final group after≤energy soko1_1.initial final UpperBudget11.Rest (before++after) := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have selected := first.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
 have restBound := endGroup_length_le UpperBudget11.Rest before
 have restSize : (endGroup UpperBudget11.Rest before).length≤18 := by
   change (endGroup UpperBudget11.Rest before).length≤10 at restBound
   omega
 have prefixNN := energy_nonnegative first UpperBudget11.Rest (by decide) (by decide)
 have split := energy_append soko1_1.initial state final UpperBudget11.Rest before after
 have compare := energy_subset first.trace last group (endGroup UpperBudget11.Rest before)
   groupUnique selected.1 subset selected.2 restSize
 omega
#print axioms subset_le
end Owner1007.RestTailBudget11
