import NetHack.SokobanLinearPhases.Map12.Walks05
import NetHack.SokobanLinearPhases.Map12.Pushes05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks05 : walkCheck soko1_2.board soko1_2.initial.holes heroes 5 = true := by
  change (([29, 30, 31, 32, 33, 34, 35, 36] ++ [55, 56, 82, 105, 106, 108, 115, 116] ++ [117, 131, 132, 133, 134, 135, 140, 141] ++ [142, 143, 157, 158, 159, 160, 161, 163] ++ [164, 166, 167, 168, 169, 184, 185, 186] ++ [187, 189, 190, 191, 192, 193, 194, 210] ++ [211, 212, 213, 214, 215, 216, 218, 219] ++ [220, 236, 237, 238, 239, 241, 242, 244] ++ [245, 246, 262, 263, 264, 265, 270, 271] ++ [272, 288, 289, 290, 291, 292, 293, 294] ++ [296, 297, 317, 318, 319, 320, 322, 345] ++ [348, 370, 371, 372, 373, 374, 396, 397] ++ [399, 400] : List Cell).all (walkRow 5)) = true
  simp only [List.all_append, walks05_part0, walks05_part1, walks05_part2, walks05_part3, walks05_part4, walks05_part5, walks05_part6, walks05_part7, walks05_part8, walks05_part9, walks05_part10, walks05_part11, walks05_part12, Bool.and_self]
theorem pushes05 : pushCheck soko1_2.board soko1_2.initial.holes heroes crates 5 = true := by
  change (([29, 30, 56, 82, 105, 106, 108, 115] ++ [116, 117, 131, 132, 133, 134, 135, 140] ++ [141, 142, 143, 157, 158, 159, 160, 161] ++ [163, 164, 166, 167, 168, 169, 184, 185] ++ [186, 187, 189, 190, 191, 192, 193, 194] ++ [210, 211, 212, 213, 214, 215, 216, 218] ++ [219, 220, 236, 237, 238, 239, 241, 242] ++ [244, 245, 246, 262, 263, 264, 265, 270] ++ [271, 272, 288, 289, 290, 291, 292, 293] ++ [294, 296, 297, 317, 318, 319, 320, 322] ++ [345, 348, 370, 371, 372, 373, 374, 397] ++ [400] : List Cell).all (pushRow 5)) = true
  simp only [List.all_append, pushes05_part0, pushes05_part1, pushes05_part2, pushes05_part3, pushes05_part4, pushes05_part5, pushes05_part6, pushes05_part7, pushes05_part8, pushes05_part9, pushes05_part10, pushes05_part11, Bool.and_self]
end NetHack.SokobanLinearPhases.Map12
