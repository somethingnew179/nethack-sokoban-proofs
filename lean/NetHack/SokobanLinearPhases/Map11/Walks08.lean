import NetHack.SokobanLinearPhases.Map11.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map11
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks08_part0 : ([27, 28, 29, 30, 31, 32, 33, 34] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part1 : ([35, 36, 37, 38, 39, 40, 41, 53] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part2 : ([54, 55, 56, 57, 58, 59, 85, 106] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part3 : ([107, 108, 109, 110, 111, 112, 113, 114] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part4 : ([115, 116, 132, 133, 134, 135, 136, 137] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part5 : ([138, 139, 140, 141, 142, 164, 183, 184] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part6 : ([185, 186, 187, 188, 189, 190, 191, 192] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part7 : ([193, 194, 209, 210, 211, 212, 213, 214] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part8 : ([215, 216, 217, 218, 219, 220, 239, 262] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part9 : ([263, 264, 265, 266, 267, 268, 269, 270] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part10 : ([271, 288, 289, 290, 291, 292, 293, 294] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part11 : ([295, 296, 297, 314, 315, 316, 317, 318] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part12 : ([319, 320, 321, 322, 345, 365, 366, 367] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part13 : ([368, 369, 370, 371, 372, 391, 392, 393] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part14 : ([394, 395, 396, 397, 398, 417, 418, 419] : List Cell).all (walkRow 8) = true := by
  decide +kernel
end NetHack.SokobanLinearPhases.Map11
