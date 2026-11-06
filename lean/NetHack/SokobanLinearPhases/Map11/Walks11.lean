import NetHack.SokobanLinearPhases.Map11.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map11
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks11_part0 : ([27, 28, 29, 30, 31, 32, 33, 34] : List Cell).all (walkRow 11) = true := by
  decide +kernel
theorem walks11_part1 : ([35, 36, 37, 38, 39, 40, 41, 42] : List Cell).all (walkRow 11) = true := by
  decide +kernel
theorem walks11_part2 : ([43, 44, 53, 54, 55, 56, 57, 58] : List Cell).all (walkRow 11) = true := by
  decide +kernel
theorem walks11_part3 : ([59, 85, 106, 107, 108, 109, 110, 111] : List Cell).all (walkRow 11) = true := by
  decide +kernel
theorem walks11_part4 : ([112, 113, 114, 115, 116, 132, 133, 134] : List Cell).all (walkRow 11) = true := by
  decide +kernel
theorem walks11_part5 : ([135, 136, 137, 138, 139, 140, 141, 142] : List Cell).all (walkRow 11) = true := by
  decide +kernel
theorem walks11_part6 : ([164, 183, 184, 185, 186, 187, 188, 189] : List Cell).all (walkRow 11) = true := by
  decide +kernel
theorem walks11_part7 : ([190, 191, 192, 193, 194, 209, 210, 211] : List Cell).all (walkRow 11) = true := by
  decide +kernel
theorem walks11_part8 : ([212, 213, 214, 215, 216, 217, 218, 219] : List Cell).all (walkRow 11) = true := by
  decide +kernel
theorem walks11_part9 : ([220, 239, 262, 263, 264, 265, 266, 267] : List Cell).all (walkRow 11) = true := by
  decide +kernel
theorem walks11_part10 : ([268, 269, 270, 271, 288, 289, 290, 291] : List Cell).all (walkRow 11) = true := by
  decide +kernel
theorem walks11_part11 : ([292, 293, 294, 295, 296, 297, 314, 315] : List Cell).all (walkRow 11) = true := by
  decide +kernel
theorem walks11_part12 : ([316, 317, 318, 319, 320, 321, 322, 345] : List Cell).all (walkRow 11) = true := by
  decide +kernel
theorem walks11_part13 : ([365, 366, 367, 368, 369, 370, 371, 372] : List Cell).all (walkRow 11) = true := by
  decide +kernel
theorem walks11_part14 : ([391, 392, 393, 394, 395, 396, 397, 398] : List Cell).all (walkRow 11) = true := by
  decide +kernel
theorem walks11_part15 : ([417, 418, 419] : List Cell).all (walkRow 11) = true := by
  decide +kernel
end NetHack.SokobanLinearPhases.Map11
