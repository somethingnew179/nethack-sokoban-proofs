import NetHack.SokobanLinearPhases.Map12.Walks06
import NetHack.SokobanLinearPhases.Map12.Pushes06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks06 : walkCheck soko1_2.board soko1_2.initial.holes heroes 6 = true := by
  change (([29, 30, 31, 32, 33, 34, 35, 36] ++ [37, 55, 56, 82, 105, 106, 108, 115] ++ [116, 117, 131, 132, 133, 134, 135, 140] ++ [141, 142, 143, 157, 158, 159, 160, 161] ++ [163, 164, 166, 167, 168, 169, 184, 185] ++ [186, 187, 189, 190, 191, 192, 193, 194] ++ [210, 211, 212, 213, 214, 215, 216, 218] ++ [219, 220, 236, 237, 238, 239, 241, 242] ++ [244, 245, 246, 262, 263, 264, 265, 270] ++ [271, 272, 288, 289, 290, 291, 292, 293] ++ [294, 296, 297, 317, 318, 319, 320, 322] ++ [345, 348, 370, 371, 372, 373, 374, 396] ++ [397, 399, 400] : List Cell).all (walkRow 6)) = true
  simp only [List.all_append, walks06_part0, walks06_part1, walks06_part2, walks06_part3, walks06_part4, walks06_part5, walks06_part6, walks06_part7, walks06_part8, walks06_part9, walks06_part10, walks06_part11, walks06_part12, Bool.and_self]
theorem pushes06 : pushCheck soko1_2.board soko1_2.initial.holes heroes crates 6 = true := by
  change (([29, 30, 56, 82, 105, 106, 108, 115] ++ [116, 117, 131, 132, 133, 134, 135, 140] ++ [141, 142, 143, 157, 158, 159, 160, 161] ++ [163, 164, 166, 167, 168, 169, 184, 185] ++ [186, 187, 189, 190, 191, 192, 193, 194] ++ [210, 211, 212, 213, 214, 215, 216, 218] ++ [219, 220, 236, 237, 238, 239, 241, 242] ++ [244, 245, 246, 262, 263, 264, 265, 270] ++ [271, 272, 288, 289, 290, 291, 292, 293] ++ [294, 296, 297, 317, 318, 319, 320, 322] ++ [345, 348, 370, 371, 372, 373, 374, 397] ++ [400] : List Cell).all (pushRow 6)) = true
  simp only [List.all_append, pushes06_part0, pushes06_part1, pushes06_part2, pushes06_part3, pushes06_part4, pushes06_part5, pushes06_part6, pushes06_part7, pushes06_part8, pushes06_part9, pushes06_part10, pushes06_part11, Bool.and_self]
end NetHack.SokobanLinearPhases.Map12
