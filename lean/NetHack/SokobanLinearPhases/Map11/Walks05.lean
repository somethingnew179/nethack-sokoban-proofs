import NetHack.SokobanLinearPhases.Map11.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map11
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks05_part0 : ([27, 28, 29, 30, 31, 32, 33, 34] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part1 : ([35, 36, 37, 38, 53, 54, 55, 56] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part2 : ([57, 58, 59, 85, 106, 107, 108, 109] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part3 : ([110, 111, 112, 113, 114, 115, 116, 132] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part4 : ([133, 134, 135, 136, 137, 138, 139, 140] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part5 : ([141, 142, 164, 183, 184, 185, 186, 187] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part6 : ([188, 189, 190, 191, 192, 193, 194, 209] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part7 : ([210, 211, 212, 213, 214, 215, 216, 217] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part8 : ([218, 219, 220, 239, 262, 263, 264, 265] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part9 : ([266, 267, 268, 269, 270, 271, 288, 289] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part10 : ([290, 291, 292, 293, 294, 295, 296, 297] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part11 : ([314, 315, 316, 317, 318, 319, 320, 321] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part12 : ([322, 345, 365, 366, 367, 368, 369, 370] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part13 : ([371, 372, 391, 392, 393, 394, 395, 396] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part14 : ([397, 398, 417, 418, 419] : List Cell).all (walkRow 5) = true := by
  decide +kernel
end NetHack.SokobanLinearPhases.Map11
