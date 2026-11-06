import NetHack.SokobanLinearPhases.Map12.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks03_part0 : ([29, 30, 31, 32, 33, 34, 55, 56] : List Cell).all (walkRow 3) = true := by
  decide +kernel
theorem walks03_part1 : ([82, 105, 106, 108, 115, 116, 117, 131] : List Cell).all (walkRow 3) = true := by
  decide +kernel
theorem walks03_part2 : ([132, 133, 134, 135, 140, 141, 142, 143] : List Cell).all (walkRow 3) = true := by
  decide +kernel
theorem walks03_part3 : ([157, 158, 159, 160, 161, 163, 164, 166] : List Cell).all (walkRow 3) = true := by
  decide +kernel
theorem walks03_part4 : ([167, 168, 169, 184, 185, 186, 187, 189] : List Cell).all (walkRow 3) = true := by
  decide +kernel
theorem walks03_part5 : ([190, 191, 192, 193, 194, 210, 211, 212] : List Cell).all (walkRow 3) = true := by
  decide +kernel
theorem walks03_part6 : ([213, 214, 215, 216, 218, 219, 220, 236] : List Cell).all (walkRow 3) = true := by
  decide +kernel
theorem walks03_part7 : ([237, 238, 239, 241, 242, 244, 245, 246] : List Cell).all (walkRow 3) = true := by
  decide +kernel
theorem walks03_part8 : ([262, 263, 264, 265, 270, 271, 272, 288] : List Cell).all (walkRow 3) = true := by
  decide +kernel
theorem walks03_part9 : ([289, 290, 291, 292, 293, 294, 296, 297] : List Cell).all (walkRow 3) = true := by
  decide +kernel
theorem walks03_part10 : ([317, 318, 319, 320, 322, 345, 348, 370] : List Cell).all (walkRow 3) = true := by
  decide +kernel
theorem walks03_part11 : ([371, 372, 373, 374, 396, 397, 399, 400] : List Cell).all (walkRow 3) = true := by
  decide +kernel
end NetHack.SokobanLinearPhases.Map12
