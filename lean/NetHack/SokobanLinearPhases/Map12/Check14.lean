import NetHack.SokobanLinearPhases.Map12.Walks14
import NetHack.SokobanLinearPhases.Map12.Pushes14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks14 : walkCheck soko1_2.board soko1_2.initial.holes heroes 14 = true := by
  change (([29, 30, 31, 32, 33, 34, 35, 36] ++ [37, 38, 39, 40, 41, 42, 43, 44] ++ [45, 55, 56, 82, 105, 106, 108, 115] ++ [116, 117, 131, 132, 133, 134, 135, 140] ++ [141, 142, 143, 157, 158, 159, 160, 161] ++ [163, 164, 166, 167, 168, 169, 184, 185] ++ [186, 187, 189, 190, 191, 192, 193, 194] ++ [210, 211, 212, 213, 214, 215, 216, 218] ++ [219, 220, 236, 237, 238, 239, 241, 242] ++ [244, 245, 246, 262, 263, 264, 265, 270] ++ [271, 272, 288, 289, 290, 291, 292, 293] ++ [294, 296, 297, 317, 318, 319, 320, 322] ++ [345, 348, 370, 371, 372, 373, 374, 396] ++ [397, 399, 400] : List Cell).all (walkRow 14)) = true
  simp only [List.all_append, walks14_part0, walks14_part1, walks14_part2, walks14_part3, walks14_part4, walks14_part5, walks14_part6, walks14_part7, walks14_part8, walks14_part9, walks14_part10, walks14_part11, walks14_part12, walks14_part13, Bool.and_self]
theorem pushes14 : pushCheck soko1_2.board soko1_2.initial.holes heroes crates 14 = true := by
  change (([29, 30, 56, 82, 105, 106, 108, 115] ++ [116, 117, 131, 132, 133, 134, 135, 140] ++ [141, 142, 143, 157, 158, 159, 160, 161] ++ [163, 164, 166, 167, 168, 169, 184, 185] ++ [186, 187, 189, 190, 191, 192, 193, 194] ++ [210, 211, 212, 213, 214, 215, 216, 218] ++ [219, 220, 236, 237, 238, 239, 241, 242] ++ [244, 245, 246, 262, 263, 264, 265, 270] ++ [271, 272, 288, 289, 290, 291, 292, 293] ++ [294, 296, 297, 317, 318, 319, 320, 322] ++ [345, 348, 370, 371, 372, 373, 374, 397] ++ [400] : List Cell).all (pushRow 14)) = true
  simp only [List.all_append, pushes14_part0, pushes14_part1, pushes14_part2, pushes14_part3, pushes14_part4, pushes14_part5, pushes14_part6, pushes14_part7, pushes14_part8, pushes14_part9, pushes14_part10, pushes14_part11, Bool.and_self]
end NetHack.SokobanLinearPhases.Map12
