import NetHack.Sokoban22Refined85.Roots
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem initial_good : Good soko2_2.board soko2_2.initial.holes 5 soko2_2.initial := by decide
theorem initial_base : Generated.soko2_2Potential.value soko2_2.initial = 73 := by decide
theorem initial_bonus : bonus soko2_2.initial.player (project soko2_2.initial.boulders) = 12 := by decide
end NetHack.Sokoban22Refined85
