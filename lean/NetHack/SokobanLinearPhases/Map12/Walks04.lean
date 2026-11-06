import NetHack.SokobanLinearPhases.Map12.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks04_part0 : ([29, 30, 31, 32, 33, 34, 35, 55] : List Cell).all (walkRow 4) = true := by
  decide +kernel
theorem walks04_part1 : ([56, 82, 105, 106, 108, 115, 116, 117] : List Cell).all (walkRow 4) = true := by
  decide +kernel
theorem walks04_part2 : ([131, 132, 133, 134, 135, 140, 141, 142] : List Cell).all (walkRow 4) = true := by
  decide +kernel
theorem walks04_part3 : ([143, 157, 158, 159, 160, 161, 163, 164] : List Cell).all (walkRow 4) = true := by
  decide +kernel
theorem walks04_part4 : ([166, 167, 168, 169, 184, 185, 186, 187] : List Cell).all (walkRow 4) = true := by
  decide +kernel
theorem walks04_part5 : ([189, 190, 191, 192, 193, 194, 210, 211] : List Cell).all (walkRow 4) = true := by
  decide +kernel
theorem walks04_part6 : ([212, 213, 214, 215, 216, 218, 219, 220] : List Cell).all (walkRow 4) = true := by
  decide +kernel
theorem walks04_part7 : ([236, 237, 238, 239, 241, 242, 244, 245] : List Cell).all (walkRow 4) = true := by
  decide +kernel
theorem walks04_part8 : ([246, 262, 263, 264, 265, 270, 271, 272] : List Cell).all (walkRow 4) = true := by
  decide +kernel
theorem walks04_part9 : ([288, 289, 290, 291, 292, 293, 294, 296] : List Cell).all (walkRow 4) = true := by
  decide +kernel
theorem walks04_part10 : ([297, 317, 318, 319, 320, 322, 345, 348] : List Cell).all (walkRow 4) = true := by
  decide +kernel
theorem walks04_part11 : ([370, 371, 372, 373, 374, 396, 397, 399] : List Cell).all (walkRow 4) = true := by
  decide +kernel
theorem walks04_part12 : ([400] : List Cell).all (walkRow 4) = true := by
  decide +kernel
end NetHack.SokobanLinearPhases.Map12
