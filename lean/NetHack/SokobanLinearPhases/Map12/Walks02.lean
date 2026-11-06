import NetHack.SokobanLinearPhases.Map12.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks02_part0 : ([29, 30, 31, 32, 33, 55, 56, 82] : List Cell).all (walkRow 2) = true := by
  decide +kernel
theorem walks02_part1 : ([105, 106, 108, 115, 116, 117, 131, 132] : List Cell).all (walkRow 2) = true := by
  decide +kernel
theorem walks02_part2 : ([133, 134, 135, 140, 141, 142, 143, 157] : List Cell).all (walkRow 2) = true := by
  decide +kernel
theorem walks02_part3 : ([158, 159, 160, 161, 163, 164, 166, 167] : List Cell).all (walkRow 2) = true := by
  decide +kernel
theorem walks02_part4 : ([168, 169, 184, 185, 186, 187, 189, 190] : List Cell).all (walkRow 2) = true := by
  decide +kernel
theorem walks02_part5 : ([191, 192, 193, 194, 210, 211, 212, 213] : List Cell).all (walkRow 2) = true := by
  decide +kernel
theorem walks02_part6 : ([214, 215, 216, 218, 219, 220, 236, 237] : List Cell).all (walkRow 2) = true := by
  decide +kernel
theorem walks02_part7 : ([238, 239, 241, 242, 244, 245, 246, 262] : List Cell).all (walkRow 2) = true := by
  decide +kernel
theorem walks02_part8 : ([263, 264, 265, 270, 271, 272, 288, 289] : List Cell).all (walkRow 2) = true := by
  decide +kernel
theorem walks02_part9 : ([290, 291, 292, 293, 294, 296, 297, 317] : List Cell).all (walkRow 2) = true := by
  decide +kernel
theorem walks02_part10 : ([318, 319, 320, 322, 345, 348, 370, 371] : List Cell).all (walkRow 2) = true := by
  decide +kernel
theorem walks02_part11 : ([372, 373, 374, 396, 397, 399, 400] : List Cell).all (walkRow 2) = true := by
  decide +kernel
end NetHack.SokobanLinearPhases.Map12
