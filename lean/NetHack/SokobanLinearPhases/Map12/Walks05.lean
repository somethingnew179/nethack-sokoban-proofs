import NetHack.SokobanLinearPhases.Map12.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks05_part0 : ([29, 30, 31, 32, 33, 34, 35, 36] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part1 : ([55, 56, 82, 105, 106, 108, 115, 116] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part2 : ([117, 131, 132, 133, 134, 135, 140, 141] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part3 : ([142, 143, 157, 158, 159, 160, 161, 163] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part4 : ([164, 166, 167, 168, 169, 184, 185, 186] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part5 : ([187, 189, 190, 191, 192, 193, 194, 210] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part6 : ([211, 212, 213, 214, 215, 216, 218, 219] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part7 : ([220, 236, 237, 238, 239, 241, 242, 244] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part8 : ([245, 246, 262, 263, 264, 265, 270, 271] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part9 : ([272, 288, 289, 290, 291, 292, 293, 294] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part10 : ([296, 297, 317, 318, 319, 320, 322, 345] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part11 : ([348, 370, 371, 372, 373, 374, 396, 397] : List Cell).all (walkRow 5) = true := by
  decide +kernel
theorem walks05_part12 : ([399, 400] : List Cell).all (walkRow 5) = true := by
  decide +kernel
end NetHack.SokobanLinearPhases.Map12
