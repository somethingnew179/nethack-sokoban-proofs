import NetHack.SokobanLinearPhases.Map11.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map11
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks06_part0 : ([27, 28, 29, 30, 31, 32, 33, 34] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part1 : ([35, 36, 37, 38, 39, 53, 54, 55] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part2 : ([56, 57, 58, 59, 85, 106, 107, 108] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part3 : ([109, 110, 111, 112, 113, 114, 115, 116] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part4 : ([132, 133, 134, 135, 136, 137, 138, 139] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part5 : ([140, 141, 142, 164, 183, 184, 185, 186] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part6 : ([187, 188, 189, 190, 191, 192, 193, 194] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part7 : ([209, 210, 211, 212, 213, 214, 215, 216] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part8 : ([217, 218, 219, 220, 239, 262, 263, 264] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part9 : ([265, 266, 267, 268, 269, 270, 271, 288] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part10 : ([289, 290, 291, 292, 293, 294, 295, 296] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part11 : ([297, 314, 315, 316, 317, 318, 319, 320] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part12 : ([321, 322, 345, 365, 366, 367, 368, 369] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part13 : ([370, 371, 372, 391, 392, 393, 394, 395] : List Cell).all (walkRow 6) = true := by
  decide +kernel
theorem walks06_part14 : ([396, 397, 398, 417, 418, 419] : List Cell).all (walkRow 6) = true := by
  decide +kernel
end NetHack.SokobanLinearPhases.Map11
