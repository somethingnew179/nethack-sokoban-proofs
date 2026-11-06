import NetHack.SokobanLinearPhases.Map11.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map11
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks10_part0 : ([27, 28, 29, 30, 31, 32, 33, 34] : List Cell).all (walkRow 10) = true := by
  decide +kernel
theorem walks10_part1 : ([35, 36, 37, 38, 39, 40, 41, 42] : List Cell).all (walkRow 10) = true := by
  decide +kernel
theorem walks10_part2 : ([43, 53, 54, 55, 56, 57, 58, 59] : List Cell).all (walkRow 10) = true := by
  decide +kernel
theorem walks10_part3 : ([85, 106, 107, 108, 109, 110, 111, 112] : List Cell).all (walkRow 10) = true := by
  decide +kernel
theorem walks10_part4 : ([113, 114, 115, 116, 132, 133, 134, 135] : List Cell).all (walkRow 10) = true := by
  decide +kernel
theorem walks10_part5 : ([136, 137, 138, 139, 140, 141, 142, 164] : List Cell).all (walkRow 10) = true := by
  decide +kernel
theorem walks10_part6 : ([183, 184, 185, 186, 187, 188, 189, 190] : List Cell).all (walkRow 10) = true := by
  decide +kernel
theorem walks10_part7 : ([191, 192, 193, 194, 209, 210, 211, 212] : List Cell).all (walkRow 10) = true := by
  decide +kernel
theorem walks10_part8 : ([213, 214, 215, 216, 217, 218, 219, 220] : List Cell).all (walkRow 10) = true := by
  decide +kernel
theorem walks10_part9 : ([239, 262, 263, 264, 265, 266, 267, 268] : List Cell).all (walkRow 10) = true := by
  decide +kernel
theorem walks10_part10 : ([269, 270, 271, 288, 289, 290, 291, 292] : List Cell).all (walkRow 10) = true := by
  decide +kernel
theorem walks10_part11 : ([293, 294, 295, 296, 297, 314, 315, 316] : List Cell).all (walkRow 10) = true := by
  decide +kernel
theorem walks10_part12 : ([317, 318, 319, 320, 321, 322, 345, 365] : List Cell).all (walkRow 10) = true := by
  decide +kernel
theorem walks10_part13 : ([366, 367, 368, 369, 370, 371, 372, 391] : List Cell).all (walkRow 10) = true := by
  decide +kernel
theorem walks10_part14 : ([392, 393, 394, 395, 396, 397, 398, 417] : List Cell).all (walkRow 10) = true := by
  decide +kernel
theorem walks10_part15 : ([418, 419] : List Cell).all (walkRow 10) = true := by
  decide +kernel
end NetHack.SokobanLinearPhases.Map11
