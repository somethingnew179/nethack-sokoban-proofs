/- Initial disjoint ghost groups. The old136 nonlinear certificate is
re-evaluated on the complementary nine actual boulders, not on group7.
This module proves no new original numerical lower bound. -/
import NetHack.Soko32Penalty5.Data
import NetHack.Sokoban32Refined.LowerBound
namespace NetHack.Soko32Disjoint
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
abbrev prior := NetHack.Sokoban32Refined.certificate
def complementary : List Cell := [80,86,113,132,134,158,161,188,211]
def bonus (hero : Cell) (group : List Cell) : Int := prior.bonus hero (project group)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem initial_partition : (NetHack.Soko32Penalty5.initialGroup ++ complementary).Perm soko3_2.initial.boulders := by decide +kernel
theorem initial_top_bonus : bonus soko3_2.initial.player complementary = 1 := by decide +kernel
end NetHack.Soko32Disjoint
