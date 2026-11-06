import NetHack.SokobanLinearPhases.Map32.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map32
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks11 : walkCheck soko3_2.board soko3_2.initial.holes heroes 11 = true := by decide +kernel
theorem pushes11 : pushCheck soko3_2.board soko3_2.initial.holes heroes crates 11 = true := by decide +kernel
end NetHack.SokobanLinearPhases.Map32
