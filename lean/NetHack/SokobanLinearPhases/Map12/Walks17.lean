import NetHack.SokobanLinearPhases.Map12.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks17_part0 : ([29, 30, 31, 32, 33, 34, 35, 36] : List Cell).all (walkRow 17) = true := by
  decide +kernel
theorem walks17_part1 : ([37, 38, 39, 40, 41, 42, 43, 44] : List Cell).all (walkRow 17) = true := by
  decide +kernel
theorem walks17_part2 : ([45, 46, 47, 48, 55, 56, 82, 105] : List Cell).all (walkRow 17) = true := by
  decide +kernel
theorem walks17_part3 : ([106, 108, 115, 116, 117, 131, 132, 133] : List Cell).all (walkRow 17) = true := by
  decide +kernel
theorem walks17_part4 : ([134, 135, 140, 141, 142, 143, 157, 158] : List Cell).all (walkRow 17) = true := by
  decide +kernel
theorem walks17_part5 : ([159, 160, 161, 163, 164, 166, 167, 168] : List Cell).all (walkRow 17) = true := by
  decide +kernel
theorem walks17_part6 : ([169, 184, 185, 186, 187, 189, 190, 191] : List Cell).all (walkRow 17) = true := by
  decide +kernel
theorem walks17_part7 : ([192, 193, 194, 210, 211, 212, 213, 214] : List Cell).all (walkRow 17) = true := by
  decide +kernel
theorem walks17_part8 : ([215, 216, 218, 219, 220, 236, 237, 238] : List Cell).all (walkRow 17) = true := by
  decide +kernel
theorem walks17_part9 : ([239, 241, 242, 244, 245, 246, 262, 263] : List Cell).all (walkRow 17) = true := by
  decide +kernel
theorem walks17_part10 : ([264, 265, 270, 271, 272, 288, 289, 290] : List Cell).all (walkRow 17) = true := by
  decide +kernel
theorem walks17_part11 : ([291, 292, 293, 294, 296, 297, 317, 318] : List Cell).all (walkRow 17) = true := by
  decide +kernel
theorem walks17_part12 : ([319, 320, 322, 345, 348, 370, 371, 372] : List Cell).all (walkRow 17) = true := by
  decide +kernel
theorem walks17_part13 : ([373, 374, 396, 397, 399, 400] : List Cell).all (walkRow 17) = true := by
  decide +kernel
end NetHack.SokobanLinearPhases.Map12
