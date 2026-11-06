import NetHack.SokobanLinearPhases.Map12.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks08_part0 : ([29, 30, 31, 32, 33, 34, 35, 36] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part1 : ([37, 38, 39, 55, 56, 82, 105, 106] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part2 : ([108, 115, 116, 117, 131, 132, 133, 134] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part3 : ([135, 140, 141, 142, 143, 157, 158, 159] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part4 : ([160, 161, 163, 164, 166, 167, 168, 169] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part5 : ([184, 185, 186, 187, 189, 190, 191, 192] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part6 : ([193, 194, 210, 211, 212, 213, 214, 215] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part7 : ([216, 218, 219, 220, 236, 237, 238, 239] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part8 : ([241, 242, 244, 245, 246, 262, 263, 264] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part9 : ([265, 270, 271, 272, 288, 289, 290, 291] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part10 : ([292, 293, 294, 296, 297, 317, 318, 319] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part11 : ([320, 322, 345, 348, 370, 371, 372, 373] : List Cell).all (walkRow 8) = true := by
  decide +kernel
theorem walks08_part12 : ([374, 396, 397, 399, 400] : List Cell).all (walkRow 8) = true := by
  decide +kernel
end NetHack.SokobanLinearPhases.Map12
