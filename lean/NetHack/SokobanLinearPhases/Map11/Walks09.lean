import NetHack.SokobanLinearPhases.Map11.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map11
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks09_part0 : ([27, 28, 29, 30, 31, 32, 33, 34] : List Cell).all (walkRow 9) = true := by
  decide +kernel
theorem walks09_part1 : ([35, 36, 37, 38, 39, 40, 41, 42] : List Cell).all (walkRow 9) = true := by
  decide +kernel
theorem walks09_part2 : ([53, 54, 55, 56, 57, 58, 59, 85] : List Cell).all (walkRow 9) = true := by
  decide +kernel
theorem walks09_part3 : ([106, 107, 108, 109, 110, 111, 112, 113] : List Cell).all (walkRow 9) = true := by
  decide +kernel
theorem walks09_part4 : ([114, 115, 116, 132, 133, 134, 135, 136] : List Cell).all (walkRow 9) = true := by
  decide +kernel
theorem walks09_part5 : ([137, 138, 139, 140, 141, 142, 164, 183] : List Cell).all (walkRow 9) = true := by
  decide +kernel
theorem walks09_part6 : ([184, 185, 186, 187, 188, 189, 190, 191] : List Cell).all (walkRow 9) = true := by
  decide +kernel
theorem walks09_part7 : ([192, 193, 194, 209, 210, 211, 212, 213] : List Cell).all (walkRow 9) = true := by
  decide +kernel
theorem walks09_part8 : ([214, 215, 216, 217, 218, 219, 220, 239] : List Cell).all (walkRow 9) = true := by
  decide +kernel
theorem walks09_part9 : ([262, 263, 264, 265, 266, 267, 268, 269] : List Cell).all (walkRow 9) = true := by
  decide +kernel
theorem walks09_part10 : ([270, 271, 288, 289, 290, 291, 292, 293] : List Cell).all (walkRow 9) = true := by
  decide +kernel
theorem walks09_part11 : ([294, 295, 296, 297, 314, 315, 316, 317] : List Cell).all (walkRow 9) = true := by
  decide +kernel
theorem walks09_part12 : ([318, 319, 320, 321, 322, 345, 365, 366] : List Cell).all (walkRow 9) = true := by
  decide +kernel
theorem walks09_part13 : ([367, 368, 369, 370, 371, 372, 391, 392] : List Cell).all (walkRow 9) = true := by
  decide +kernel
theorem walks09_part14 : ([393, 394, 395, 396, 397, 398, 417, 418] : List Cell).all (walkRow 9) = true := by
  decide +kernel
theorem walks09_part15 : ([419] : List Cell).all (walkRow 9) = true := by
  decide +kernel
end NetHack.SokobanLinearPhases.Map11
