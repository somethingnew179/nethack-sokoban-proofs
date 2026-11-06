import NetHack.SokobanLinearPhases.Map11.Walks06
import NetHack.SokobanLinearPhases.Map11.Pushes06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map11
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks06 : walkCheck soko1_1.board soko1_1.initial.holes heroes 6 = true := by
  change (([27, 28, 29, 30, 31, 32, 33, 34] ++ [35, 36, 37, 38, 39, 53, 54, 55] ++ [56, 57, 58, 59, 85, 106, 107, 108] ++ [109, 110, 111, 112, 113, 114, 115, 116] ++ [132, 133, 134, 135, 136, 137, 138, 139] ++ [140, 141, 142, 164, 183, 184, 185, 186] ++ [187, 188, 189, 190, 191, 192, 193, 194] ++ [209, 210, 211, 212, 213, 214, 215, 216] ++ [217, 218, 219, 220, 239, 262, 263, 264] ++ [265, 266, 267, 268, 269, 270, 271, 288] ++ [289, 290, 291, 292, 293, 294, 295, 296] ++ [297, 314, 315, 316, 317, 318, 319, 320] ++ [321, 322, 345, 365, 366, 367, 368, 369] ++ [370, 371, 372, 391, 392, 393, 394, 395] ++ [396, 397, 398, 417, 418, 419] : List Cell).all (walkRow 6)) = true
  simp only [List.all_append, walks06_part0, walks06_part1, walks06_part2, walks06_part3, walks06_part4, walks06_part5, walks06_part6, walks06_part7, walks06_part8, walks06_part9, walks06_part10, walks06_part11, walks06_part12, walks06_part13, walks06_part14, Bool.and_self]
theorem pushes06 : pushCheck soko1_1.board soko1_1.initial.holes heroes crates 6 = true := by
  change (([27, 28, 29, 30, 31, 32, 33, 59] ++ [85, 106, 107, 108, 109, 110, 111, 112] ++ [113, 114, 115, 116, 132, 133, 134, 135] ++ [136, 137, 138, 139, 140, 141, 142, 164] ++ [183, 184, 185, 186, 187, 188, 189, 190] ++ [191, 192, 193, 194, 209, 210, 211, 212] ++ [213, 214, 215, 216, 217, 218, 219, 220] ++ [239, 262, 263, 264, 265, 266, 267, 268] ++ [269, 270, 271, 288, 289, 290, 291, 292] ++ [293, 294, 295, 296, 297, 314, 315, 316] ++ [317, 318, 319, 320, 321, 322, 345, 365] ++ [366, 367, 368, 369, 370, 371, 372, 391] ++ [392, 393, 394, 395, 396, 397, 398, 417] ++ [418, 419] : List Cell).all (pushRow 6)) = true
  simp only [List.all_append, pushes06_part0, pushes06_part1, pushes06_part2, pushes06_part3, pushes06_part4, pushes06_part5, pushes06_part6, pushes06_part7, pushes06_part8, pushes06_part9, pushes06_part10, pushes06_part11, pushes06_part12, pushes06_part13, Bool.and_self]
end NetHack.SokobanLinearPhases.Map11
