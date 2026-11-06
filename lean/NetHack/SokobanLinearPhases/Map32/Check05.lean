import NetHack.SokobanLinearPhases.Map32.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map32
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks05 : walkCheck soko3_2.board soko3_2.initial.holes heroes 5 = true := by decide +kernel
theorem pushes05 : pushCheck soko3_2.board soko3_2.initial.holes heroes crates 5 = true := by decide +kernel
end NetHack.SokobanLinearPhases.Map32
