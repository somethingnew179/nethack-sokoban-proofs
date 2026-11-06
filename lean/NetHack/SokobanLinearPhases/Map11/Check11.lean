import NetHack.SokobanLinearPhases.Map11.Walks11
import NetHack.SokobanLinearPhases.Map11.Pushes11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map11
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks11 : walkCheck soko1_1.board soko1_1.initial.holes heroes 11 = true := by
  change (([27, 28, 29, 30, 31, 32, 33, 34] ++ [35, 36, 37, 38, 39, 40, 41, 42] ++ [43, 44, 53, 54, 55, 56, 57, 58] ++ [59, 85, 106, 107, 108, 109, 110, 111] ++ [112, 113, 114, 115, 116, 132, 133, 134] ++ [135, 136, 137, 138, 139, 140, 141, 142] ++ [164, 183, 184, 185, 186, 187, 188, 189] ++ [190, 191, 192, 193, 194, 209, 210, 211] ++ [212, 213, 214, 215, 216, 217, 218, 219] ++ [220, 239, 262, 263, 264, 265, 266, 267] ++ [268, 269, 270, 271, 288, 289, 290, 291] ++ [292, 293, 294, 295, 296, 297, 314, 315] ++ [316, 317, 318, 319, 320, 321, 322, 345] ++ [365, 366, 367, 368, 369, 370, 371, 372] ++ [391, 392, 393, 394, 395, 396, 397, 398] ++ [417, 418, 419] : List Cell).all (walkRow 11)) = true
  simp only [List.all_append, walks11_part0, walks11_part1, walks11_part2, walks11_part3, walks11_part4, walks11_part5, walks11_part6, walks11_part7, walks11_part8, walks11_part9, walks11_part10, walks11_part11, walks11_part12, walks11_part13, walks11_part14, walks11_part15, Bool.and_self]
theorem pushes11 : pushCheck soko1_1.board soko1_1.initial.holes heroes crates 11 = true := by
  change (([27, 28, 29, 30, 31, 32, 33, 59] ++ [85, 106, 107, 108, 109, 110, 111, 112] ++ [113, 114, 115, 116, 132, 133, 134, 135] ++ [136, 137, 138, 139, 140, 141, 142, 164] ++ [183, 184, 185, 186, 187, 188, 189, 190] ++ [191, 192, 193, 194, 209, 210, 211, 212] ++ [213, 214, 215, 216, 217, 218, 219, 220] ++ [239, 262, 263, 264, 265, 266, 267, 268] ++ [269, 270, 271, 288, 289, 290, 291, 292] ++ [293, 294, 295, 296, 297, 314, 315, 316] ++ [317, 318, 319, 320, 321, 322, 345, 365] ++ [366, 367, 368, 369, 370, 371, 372, 391] ++ [392, 393, 394, 395, 396, 397, 398, 417] ++ [418, 419] : List Cell).all (pushRow 11)) = true
  simp only [List.all_append, pushes11_part0, pushes11_part1, pushes11_part2, pushes11_part3, pushes11_part4, pushes11_part5, pushes11_part6, pushes11_part7, pushes11_part8, pushes11_part9, pushes11_part10, pushes11_part11, pushes11_part12, pushes11_part13, Bool.and_self]
end NetHack.SokobanLinearPhases.Map11
