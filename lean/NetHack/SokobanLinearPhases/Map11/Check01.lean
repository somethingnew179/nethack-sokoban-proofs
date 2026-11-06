import NetHack.SokobanLinearPhases.Map11.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map11
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem walks01_part0 : ([27, 28, 29, 30, 31, 32, 33, 34, 53, 54, 55, 56, 57, 58, 59, 85, 106, 107, 108, 109, 110, 111, 112, 113] : List Cell).all (walkRow 1) = true := by decide +kernel
theorem walks01_part1 : ([114, 115, 116, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 164, 183, 184, 185, 186, 187, 188, 189, 190, 191] : List Cell).all (walkRow 1) = true := by decide +kernel
theorem walks01_part2 : ([192, 193, 194, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 239, 262, 263, 264, 265, 266, 267, 268, 269] : List Cell).all (walkRow 1) = true := by decide +kernel
theorem walks01_part3 : ([270, 271, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 314, 315, 316, 317, 318, 319, 320, 321, 322, 345, 365, 366] : List Cell).all (walkRow 1) = true := by decide +kernel
theorem walks01_part4 : ([367, 368, 369, 370, 371, 372, 391, 392, 393, 394, 395, 396, 397, 398, 417, 418, 419] : List Cell).all (walkRow 1) = true := by decide +kernel
theorem walks01 : walkCheck soko1_1.board soko1_1.initial.holes heroes 1 = true := by
  change (([27, 28, 29, 30, 31, 32, 33, 34, 53, 54, 55, 56, 57, 58, 59, 85, 106, 107, 108, 109, 110, 111, 112, 113] ++ [114, 115, 116, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 164, 183, 184, 185, 186, 187, 188, 189, 190, 191] ++ [192, 193, 194, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 239, 262, 263, 264, 265, 266, 267, 268, 269] ++ [270, 271, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 314, 315, 316, 317, 318, 319, 320, 321, 322, 345, 365, 366] ++ [367, 368, 369, 370, 371, 372, 391, 392, 393, 394, 395, 396, 397, 398, 417, 418, 419] : List Cell).all (walkRow 1)) = true
  simp only [List.all_append, walks01_part0, walks01_part1, walks01_part2, walks01_part3, walks01_part4, Bool.and_self]
theorem pushes01_part0 : ([27, 28, 29, 30, 31, 32, 33, 59, 85, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 132, 133, 134, 135] : List Cell).all (pushRow 1) = true := by decide +kernel
theorem pushes01_part1 : ([136, 137, 138, 139, 140, 141, 142, 164, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 209, 210, 211, 212] : List Cell).all (pushRow 1) = true := by decide +kernel
theorem pushes01_part2 : ([213, 214, 215, 216, 217, 218, 219, 220, 239, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 288, 289, 290, 291, 292] : List Cell).all (pushRow 1) = true := by decide +kernel
theorem pushes01_part3 : ([293, 294, 295, 296, 297, 314, 315, 316, 317, 318, 319, 320, 321, 322, 345, 365, 366, 367, 368, 369, 370, 371, 372, 391] : List Cell).all (pushRow 1) = true := by decide +kernel
theorem pushes01_part4 : ([392, 393, 394, 395, 396, 397, 398, 417, 418, 419] : List Cell).all (pushRow 1) = true := by decide +kernel
theorem pushes01 : pushCheck soko1_1.board soko1_1.initial.holes heroes crates 1 = true := by
  change (([27, 28, 29, 30, 31, 32, 33, 59, 85, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 132, 133, 134, 135] ++ [136, 137, 138, 139, 140, 141, 142, 164, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 209, 210, 211, 212] ++ [213, 214, 215, 216, 217, 218, 219, 220, 239, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 288, 289, 290, 291, 292] ++ [293, 294, 295, 296, 297, 314, 315, 316, 317, 318, 319, 320, 321, 322, 345, 365, 366, 367, 368, 369, 370, 371, 372, 391] ++ [392, 393, 394, 395, 396, 397, 398, 417, 418, 419] : List Cell).all (pushRow 1)) = true
  simp only [List.all_append, pushes01_part0, pushes01_part1, pushes01_part2, pushes01_part3, pushes01_part4, Bool.and_self]
end NetHack.SokobanLinearPhases.Map11
