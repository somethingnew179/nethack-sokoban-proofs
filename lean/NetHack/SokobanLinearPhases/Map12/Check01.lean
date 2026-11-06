import NetHack.SokobanLinearPhases.Map12.Walks01
import NetHack.SokobanLinearPhases.Map12.Pushes01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks01 : walkCheck soko1_2.board soko1_2.initial.holes heroes 1 = true := by
  change (([29, 30, 31, 32, 55, 56, 82, 105] ++ [106, 108, 115, 116, 117, 131, 132, 133] ++ [134, 135, 140, 141, 142, 143, 157, 158] ++ [159, 160, 161, 163, 164, 166, 167, 168] ++ [169, 184, 185, 186, 187, 189, 190, 191] ++ [192, 193, 194, 210, 211, 212, 213, 214] ++ [215, 216, 218, 219, 220, 236, 237, 238] ++ [239, 241, 242, 244, 245, 246, 262, 263] ++ [264, 265, 270, 271, 272, 288, 289, 290] ++ [291, 292, 293, 294, 296, 297, 317, 318] ++ [319, 320, 322, 345, 348, 370, 371, 372] ++ [373, 374, 396, 397, 399, 400] : List Cell).all (walkRow 1)) = true
  simp only [List.all_append, walks01_part0, walks01_part1, walks01_part2, walks01_part3, walks01_part4, walks01_part5, walks01_part6, walks01_part7, walks01_part8, walks01_part9, walks01_part10, walks01_part11, Bool.and_self]
theorem pushes01 : pushCheck soko1_2.board soko1_2.initial.holes heroes crates 1 = true := by
  change (([29, 30, 56, 82, 105, 106, 108, 115] ++ [116, 117, 131, 132, 133, 134, 135, 140] ++ [141, 142, 143, 157, 158, 159, 160, 161] ++ [163, 164, 166, 167, 168, 169, 184, 185] ++ [186, 187, 189, 190, 191, 192, 193, 194] ++ [210, 211, 212, 213, 214, 215, 216, 218] ++ [219, 220, 236, 237, 238, 239, 241, 242] ++ [244, 245, 246, 262, 263, 264, 265, 270] ++ [271, 272, 288, 289, 290, 291, 292, 293] ++ [294, 296, 297, 317, 318, 319, 320, 322] ++ [345, 348, 370, 371, 372, 373, 374, 397] ++ [400] : List Cell).all (pushRow 1)) = true
  simp only [List.all_append, pushes01_part0, pushes01_part1, pushes01_part2, pushes01_part3, pushes01_part4, pushes01_part5, pushes01_part6, pushes01_part7, pushes01_part8, pushes01_part9, pushes01_part10, pushes01_part11, Bool.and_self]
end NetHack.SokobanLinearPhases.Map12
