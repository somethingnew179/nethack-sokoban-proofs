import NetHack.SokobanLinearPhases.Map12.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks15_part0 : ([29, 30, 31, 32, 33, 34, 35, 36] : List Cell).all (walkRow 15) = true := by
  decide +kernel
theorem walks15_part1 : ([37, 38, 39, 40, 41, 42, 43, 44] : List Cell).all (walkRow 15) = true := by
  decide +kernel
theorem walks15_part2 : ([45, 46, 55, 56, 82, 105, 106, 108] : List Cell).all (walkRow 15) = true := by
  decide +kernel
theorem walks15_part3 : ([115, 116, 117, 131, 132, 133, 134, 135] : List Cell).all (walkRow 15) = true := by
  decide +kernel
theorem walks15_part4 : ([140, 141, 142, 143, 157, 158, 159, 160] : List Cell).all (walkRow 15) = true := by
  decide +kernel
theorem walks15_part5 : ([161, 163, 164, 166, 167, 168, 169, 184] : List Cell).all (walkRow 15) = true := by
  decide +kernel
theorem walks15_part6 : ([185, 186, 187, 189, 190, 191, 192, 193] : List Cell).all (walkRow 15) = true := by
  decide +kernel
theorem walks15_part7 : ([194, 210, 211, 212, 213, 214, 215, 216] : List Cell).all (walkRow 15) = true := by
  decide +kernel
theorem walks15_part8 : ([218, 219, 220, 236, 237, 238, 239, 241] : List Cell).all (walkRow 15) = true := by
  decide +kernel
theorem walks15_part9 : ([242, 244, 245, 246, 262, 263, 264, 265] : List Cell).all (walkRow 15) = true := by
  decide +kernel
theorem walks15_part10 : ([270, 271, 272, 288, 289, 290, 291, 292] : List Cell).all (walkRow 15) = true := by
  decide +kernel
theorem walks15_part11 : ([293, 294, 296, 297, 317, 318, 319, 320] : List Cell).all (walkRow 15) = true := by
  decide +kernel
theorem walks15_part12 : ([322, 345, 348, 370, 371, 372, 373, 374] : List Cell).all (walkRow 15) = true := by
  decide +kernel
theorem walks15_part13 : ([396, 397, 399, 400] : List Cell).all (walkRow 15) = true := by
  decide +kernel
end NetHack.SokobanLinearPhases.Map12
