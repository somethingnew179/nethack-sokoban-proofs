import NetHack.SokobanLinearPhases.Map12.Walks02
import NetHack.SokobanLinearPhases.Map12.Pushes02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks02 : walkCheck soko1_2.board soko1_2.initial.holes heroes 2 = true := by
  change (([29, 30, 31, 32, 33, 55, 56, 82] ++ [105, 106, 108, 115, 116, 117, 131, 132] ++ [133, 134, 135, 140, 141, 142, 143, 157] ++ [158, 159, 160, 161, 163, 164, 166, 167] ++ [168, 169, 184, 185, 186, 187, 189, 190] ++ [191, 192, 193, 194, 210, 211, 212, 213] ++ [214, 215, 216, 218, 219, 220, 236, 237] ++ [238, 239, 241, 242, 244, 245, 246, 262] ++ [263, 264, 265, 270, 271, 272, 288, 289] ++ [290, 291, 292, 293, 294, 296, 297, 317] ++ [318, 319, 320, 322, 345, 348, 370, 371] ++ [372, 373, 374, 396, 397, 399, 400] : List Cell).all (walkRow 2)) = true
  simp only [List.all_append, walks02_part0, walks02_part1, walks02_part2, walks02_part3, walks02_part4, walks02_part5, walks02_part6, walks02_part7, walks02_part8, walks02_part9, walks02_part10, walks02_part11, Bool.and_self]
theorem pushes02 : pushCheck soko1_2.board soko1_2.initial.holes heroes crates 2 = true := by
  change (([29, 30, 56, 82, 105, 106, 108, 115] ++ [116, 117, 131, 132, 133, 134, 135, 140] ++ [141, 142, 143, 157, 158, 159, 160, 161] ++ [163, 164, 166, 167, 168, 169, 184, 185] ++ [186, 187, 189, 190, 191, 192, 193, 194] ++ [210, 211, 212, 213, 214, 215, 216, 218] ++ [219, 220, 236, 237, 238, 239, 241, 242] ++ [244, 245, 246, 262, 263, 264, 265, 270] ++ [271, 272, 288, 289, 290, 291, 292, 293] ++ [294, 296, 297, 317, 318, 319, 320, 322] ++ [345, 348, 370, 371, 372, 373, 374, 397] ++ [400] : List Cell).all (pushRow 2)) = true
  simp only [List.all_append, pushes02_part0, pushes02_part1, pushes02_part2, pushes02_part3, pushes02_part4, pushes02_part5, pushes02_part6, pushes02_part7, pushes02_part8, pushes02_part9, pushes02_part10, pushes02_part11, Bool.and_self]
end NetHack.SokobanLinearPhases.Map12
