import NetHack.SokobanLinearPhases.Map12.Walks16
import NetHack.SokobanLinearPhases.Map12.Pushes16
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks16 : walkCheck soko1_2.board soko1_2.initial.holes heroes 16 = true := by
  change (([29, 30, 31, 32, 33, 34, 35, 36] ++ [37, 38, 39, 40, 41, 42, 43, 44] ++ [45, 46, 47, 55, 56, 82, 105, 106] ++ [108, 115, 116, 117, 131, 132, 133, 134] ++ [135, 140, 141, 142, 143, 157, 158, 159] ++ [160, 161, 163, 164, 166, 167, 168, 169] ++ [184, 185, 186, 187, 189, 190, 191, 192] ++ [193, 194, 210, 211, 212, 213, 214, 215] ++ [216, 218, 219, 220, 236, 237, 238, 239] ++ [241, 242, 244, 245, 246, 262, 263, 264] ++ [265, 270, 271, 272, 288, 289, 290, 291] ++ [292, 293, 294, 296, 297, 317, 318, 319] ++ [320, 322, 345, 348, 370, 371, 372, 373] ++ [374, 396, 397, 399, 400] : List Cell).all (walkRow 16)) = true
  simp only [List.all_append, walks16_part0, walks16_part1, walks16_part2, walks16_part3, walks16_part4, walks16_part5, walks16_part6, walks16_part7, walks16_part8, walks16_part9, walks16_part10, walks16_part11, walks16_part12, walks16_part13, Bool.and_self]
theorem pushes16 : pushCheck soko1_2.board soko1_2.initial.holes heroes crates 16 = true := by
  change (([29, 30, 56, 82, 105, 106, 108, 115] ++ [116, 117, 131, 132, 133, 134, 135, 140] ++ [141, 142, 143, 157, 158, 159, 160, 161] ++ [163, 164, 166, 167, 168, 169, 184, 185] ++ [186, 187, 189, 190, 191, 192, 193, 194] ++ [210, 211, 212, 213, 214, 215, 216, 218] ++ [219, 220, 236, 237, 238, 239, 241, 242] ++ [244, 245, 246, 262, 263, 264, 265, 270] ++ [271, 272, 288, 289, 290, 291, 292, 293] ++ [294, 296, 297, 317, 318, 319, 320, 322] ++ [345, 348, 370, 371, 372, 373, 374, 397] ++ [400] : List Cell).all (pushRow 16)) = true
  simp only [List.all_append, pushes16_part0, pushes16_part1, pushes16_part2, pushes16_part3, pushes16_part4, pushes16_part5, pushes16_part6, pushes16_part7, pushes16_part8, pushes16_part9, pushes16_part10, pushes16_part11, Bool.and_self]
end NetHack.SokobanLinearPhases.Map12
