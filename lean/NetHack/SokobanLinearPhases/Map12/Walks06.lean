import NetHack.SokobanLinearPhases.Map12.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks06_part0 : ([29, 30, 31, 32, 33, 34, 35, 36] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part1 : ([37, 55, 56, 82, 105, 106, 108, 115] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part2 : ([116, 117, 131, 132, 133, 134, 135, 140] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part3 : ([141, 142, 143, 157, 158, 159, 160, 161] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part4 : ([163, 164, 166, 167, 168, 169, 184, 185] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part5 : ([186, 187, 189, 190, 191, 192, 193, 194] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part6 : ([210, 211, 212, 213, 214, 215, 216, 218] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part7 : ([219, 220, 236, 237, 238, 239, 241, 242] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part8 : ([244, 245, 246, 262, 263, 264, 265, 270] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part9 : ([271, 272, 288, 289, 290, 291, 292, 293] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part10 : ([294, 296, 297, 317, 318, 319, 320, 322] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part11 : ([345, 348, 370, 371, 372, 373, 374, 396] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part12 : ([397, 399, 400] : List Cell).all (walkRow 6) = true := by
  decide +kernel
end NetHack.SokobanLinearPhases.Map12
