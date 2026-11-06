import NetHack.SokobanLinearPhases.Map12.Walks10
import NetHack.SokobanLinearPhases.Map12.Pushes10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks10 : walkCheck soko1_2.board soko1_2.initial.holes heroes 10 = true := by
  change (([29, 30, 31, 32, 33, 34, 35, 36] ++ [37, 38, 39, 40, 41, 55, 56, 82] ++ [105, 106, 108, 115, 116, 117, 131, 132] ++ [133, 134, 135, 140, 141, 142, 143, 157] ++ [158, 159, 160, 161, 163, 164, 166, 167] ++ [168, 169, 184, 185, 186, 187, 189, 190] ++ [191, 192, 193, 194, 210, 211, 212, 213] ++ [214, 215, 216, 218, 219, 220, 236, 237] ++ [238, 239, 241, 242, 244, 245, 246, 262] ++ [263, 264, 265, 270, 271, 272, 288, 289] ++ [290, 291, 292, 293, 294, 296, 297, 317] ++ [318, 319, 320, 322, 345, 348, 370, 371] ++ [372, 373, 374, 396, 397, 399, 400] : List Cell).all (walkRow 10)) = true
  simp only [List.all_append, walks10_part0, walks10_part1, walks10_part2, walks10_part3, walks10_part4, walks10_part5, walks10_part6, walks10_part7, walks10_part8, walks10_part9, walks10_part10, walks10_part11, walks10_part12, Bool.and_self]
theorem pushes10 : pushCheck soko1_2.board soko1_2.initial.holes heroes crates 10 = true := by
  change (([29, 30, 56, 82, 105, 106, 108, 115] ++ [116, 117, 131, 132, 133, 134, 135, 140] ++ [141, 142, 143, 157, 158, 159, 160, 161] ++ [163, 164, 166, 167, 168, 169, 184, 185] ++ [186, 187, 189, 190, 191, 192, 193, 194] ++ [210, 211, 212, 213, 214, 215, 216, 218] ++ [219, 220, 236, 237, 238, 239, 241, 242] ++ [244, 245, 246, 262, 263, 264, 265, 270] ++ [271, 272, 288, 289, 290, 291, 292, 293] ++ [294, 296, 297, 317, 318, 319, 320, 322] ++ [345, 348, 370, 371, 372, 373, 374, 397] ++ [400] : List Cell).all (pushRow 10)) = true
  simp only [List.all_append, pushes10_part0, pushes10_part1, pushes10_part2, pushes10_part3, pushes10_part4, pushes10_part5, pushes10_part6, pushes10_part7, pushes10_part8, pushes10_part9, pushes10_part10, pushes10_part11, Bool.and_self]
end NetHack.SokobanLinearPhases.Map12
