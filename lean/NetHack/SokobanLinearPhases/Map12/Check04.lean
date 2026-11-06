import NetHack.SokobanLinearPhases.Map12.Walks04
import NetHack.SokobanLinearPhases.Map12.Pushes04
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks04 : walkCheck soko1_2.board soko1_2.initial.holes heroes 4 = true := by
  change (([29, 30, 31, 32, 33, 34, 35, 55] ++ [56, 82, 105, 106, 108, 115, 116, 117] ++ [131, 132, 133, 134, 135, 140, 141, 142] ++ [143, 157, 158, 159, 160, 161, 163, 164] ++ [166, 167, 168, 169, 184, 185, 186, 187] ++ [189, 190, 191, 192, 193, 194, 210, 211] ++ [212, 213, 214, 215, 216, 218, 219, 220] ++ [236, 237, 238, 239, 241, 242, 244, 245] ++ [246, 262, 263, 264, 265, 270, 271, 272] ++ [288, 289, 290, 291, 292, 293, 294, 296] ++ [297, 317, 318, 319, 320, 322, 345, 348] ++ [370, 371, 372, 373, 374, 396, 397, 399] ++ [400] : List Cell).all (walkRow 4)) = true
  simp only [List.all_append, walks04_part0, walks04_part1, walks04_part2, walks04_part3, walks04_part4, walks04_part5, walks04_part6, walks04_part7, walks04_part8, walks04_part9, walks04_part10, walks04_part11, walks04_part12, Bool.and_self]
theorem pushes04 : pushCheck soko1_2.board soko1_2.initial.holes heroes crates 4 = true := by
  change (([29, 30, 56, 82, 105, 106, 108, 115] ++ [116, 117, 131, 132, 133, 134, 135, 140] ++ [141, 142, 143, 157, 158, 159, 160, 161] ++ [163, 164, 166, 167, 168, 169, 184, 185] ++ [186, 187, 189, 190, 191, 192, 193, 194] ++ [210, 211, 212, 213, 214, 215, 216, 218] ++ [219, 220, 236, 237, 238, 239, 241, 242] ++ [244, 245, 246, 262, 263, 264, 265, 270] ++ [271, 272, 288, 289, 290, 291, 292, 293] ++ [294, 296, 297, 317, 318, 319, 320, 322] ++ [345, 348, 370, 371, 372, 373, 374, 397] ++ [400] : List Cell).all (pushRow 4)) = true
  simp only [List.all_append, pushes04_part0, pushes04_part1, pushes04_part2, pushes04_part3, pushes04_part4, pushes04_part5, pushes04_part6, pushes04_part7, pushes04_part8, pushes04_part9, pushes04_part10, pushes04_part11, Bool.and_self]
end NetHack.SokobanLinearPhases.Map12
