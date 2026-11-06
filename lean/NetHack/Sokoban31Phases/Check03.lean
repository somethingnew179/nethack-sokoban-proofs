import NetHack.Sokoban31Phases.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban31Phases
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks03 : walkCheck soko3_1.board soko3_1.initial.holes heroes 3 = true := by decide +kernel
theorem pushes03 : pushCheck soko3_1.board soko3_1.initial.holes heroes crates 3 = true := by decide +kernel
end NetHack.Sokoban31Phases
