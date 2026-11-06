/- Whole-floor connected supports, kernel-checked for all8 original maps. -/
import NetHack.Sokoban.ClosedSupport
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.ClosedComponents
open ClosedSupport
def soko1_1Support : List Cell := [27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 53, 54, 55, 56, 57, 58, 59, 76, 85, 102, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 128, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 154, 164, 180, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 206, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 232, 239, 258, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 284, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 310, 314, 315, 316, 317, 318, 319, 320, 321, 322, 336, 345, 362, 365, 366, 367, 368, 369, 370, 371, 372, 391, 392, 393, 394, 395, 396, 397, 398, 417, 418, 419]
theorem soko1_1_closed_checked : check soko1_1.board soko1_1Support = true := by decide
theorem soko1_1_support_unique : soko1_1Support.Nodup := by decide
theorem soko1_1_initial_within : Within soko1_1Support soko1_1.initial := by decide
theorem soko1_1_every_trace_within {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_1.board soko1_1.initial directions final pushes moves) : Within soko1_1Support final :=
  trace_within (check_sound _ _ soko1_1_closed_checked) trace soko1_1_initial_within
def soko1_2Support : List Cell := [29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 55, 56, 76, 82, 102, 105, 106, 108, 115, 116, 117, 128, 131, 132, 133, 134, 135, 140, 141, 142, 143, 154, 157, 158, 159, 160, 161, 163, 164, 166, 167, 168, 169, 180, 184, 185, 186, 187, 189, 190, 191, 192, 193, 194, 206, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 232, 236, 237, 238, 239, 241, 242, 244, 245, 246, 258, 262, 263, 264, 265, 270, 271, 272, 284, 288, 289, 290, 291, 292, 293, 294, 296, 297, 310, 317, 318, 319, 320, 322, 336, 345, 348, 370, 371, 372, 373, 374, 396, 397, 399, 400]
theorem soko1_2_closed_checked : check soko1_2.board soko1_2Support = true := by decide
theorem soko1_2_support_unique : soko1_2Support.Nodup := by decide
theorem soko1_2_initial_within : Within soko1_2Support soko1_2.initial := by decide
theorem soko1_2_every_trace_within {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_2.board soko1_2.initial directions final pushes moves) : Within soko1_2Support final :=
  trace_within (check_sound _ _ soko1_2_closed_checked) trace soko1_2_initial_within
def soko2_1Support : List Cell := [21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 41, 42, 43, 44, 45, 47, 48, 50, 52, 61, 62, 64, 65, 66, 67, 68, 70, 71, 72, 82, 84, 85, 87, 88, 90, 92, 101, 102, 103, 106, 107, 108, 109, 110, 111, 112, 121, 122, 123, 125, 126, 127, 129, 130, 131, 141, 142, 143, 145, 146, 148, 149, 150, 162, 163, 165, 166, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 201, 202, 203, 205, 206]
theorem soko2_1_closed_checked : check soko2_1.board soko2_1Support = true := by decide
theorem soko2_1_support_unique : soko2_1Support.Nodup := by decide
theorem soko2_1_initial_within : Within soko2_1Support soko2_1.initial := by decide
theorem soko2_1_every_trace_within {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko2_1.board soko2_1.initial directions final pushes moves) : Within soko2_1Support final :=
  trace_within (check_sound _ _ soko2_1_closed_checked) trace soko2_1_initial_within
def soko2_2Support : List Cell := [25, 27, 28, 29, 30, 45, 46, 47, 48, 49, 50, 51, 52, 67, 69, 70, 71, 73, 74, 76, 89, 90, 91, 93, 94, 95, 96, 97, 98, 111, 113, 114, 115, 116, 118, 119, 120, 133, 134, 135, 136, 138, 141, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 177, 180, 181, 182, 184, 185, 186, 199, 200, 201, 202, 204, 223, 224, 225, 226, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260]
theorem soko2_2_closed_checked : check soko2_2.board soko2_2Support = true := by decide
theorem soko2_2_support_unique : soko2_2Support.Nodup := by decide
theorem soko2_2_initial_within : Within soko2_2Support soko2_2.initial := by decide
theorem soko2_2_every_trace_within {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko2_2.board soko2_2.initial directions final pushes moves) : Within soko2_2Support final :=
  trace_within (check_sound _ _ soko2_2_closed_checked) trace soko2_2_initial_within
def soko3_1Support : List Cell := [30, 31, 32, 33, 35, 36, 37, 38, 59, 60, 61, 62, 64, 65, 66, 67, 68, 69, 88, 89, 90, 91, 92, 93, 94, 95, 96, 117, 118, 119, 120, 122, 123, 124, 125, 147, 175, 176, 177, 178, 180, 181, 182, 183, 184, 204, 205, 206, 207, 209, 210, 211, 212, 213, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 262, 263, 264, 265, 267, 268, 269, 270, 271, 291, 292, 293, 294, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317]
theorem soko3_1_closed_checked : check soko3_1.board soko3_1Support = true := by decide
theorem soko3_1_support_unique : soko3_1Support.Nodup := by decide
theorem soko3_1_initial_within : Within soko3_1Support soko3_1.initial := by decide
theorem soko3_1_every_trace_within {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko3_1.board soko3_1.initial directions final pushes moves) : Within soko3_1Support final :=
  trace_within (check_sound _ _ soko3_1_closed_checked) trace soko3_1_initial_within
def soko3_2Support : List Cell := [28, 29, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 79, 80, 86, 88, 105, 106, 108, 109, 110, 112, 113, 114, 131, 132, 133, 134, 135, 136, 137, 138, 139, 157, 158, 159, 160, 161, 162, 163, 165, 166, 183, 188, 189, 192, 209, 210, 211, 212, 213, 214, 215, 216, 218, 235, 239, 241, 242, 243, 244, 245, 261, 262, 263, 265, 266, 267, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 317, 318, 320, 321]
theorem soko3_2_closed_checked : check soko3_2.board soko3_2Support = true := by decide
theorem soko3_2_support_unique : soko3_2Support.Nodup := by decide
theorem soko3_2_initial_within : Within soko3_2Support soko3_2.initial := by decide
theorem soko3_2_every_trace_within {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko3_2.board soko3_2.initial directions final pushes moves) : Within soko3_2Support final :=
  trace_within (check_sound _ _ soko3_2_closed_checked) trace soko3_2_initial_within
def soko4_1Support : List Cell := [15, 16, 17, 18, 23, 24, 25, 29, 30, 31, 32, 37, 38, 39, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 57, 58, 62, 66, 67, 80, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 96, 99, 100, 106, 107, 108, 109, 110, 114, 120, 121, 122, 123, 124, 128, 134, 135, 136, 137, 138, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 156, 157]
theorem soko4_1_closed_checked : check soko4_1.board soko4_1Support = true := by decide
theorem soko4_1_support_unique : soko4_1Support.Nodup := by decide
theorem soko4_1_initial_within : Within soko4_1Support soko4_1.initial := by decide
theorem soko4_1_every_trace_within {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko4_1.board soko4_1.initial directions final pushes moves) : Within soko4_1Support final :=
  trace_within (check_sound _ _ soko4_1_closed_checked) trace soko4_1_initial_within
def soko4_2Support : List Cell := [16, 18, 19, 20, 21, 25, 26, 27, 28, 31, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 46, 49, 50, 51, 52, 54, 55, 56, 57, 58, 61, 64, 65, 66, 67, 69, 70, 71, 72, 73, 76, 84, 91, 98, 99, 100, 101, 102, 103, 106, 113, 114, 115, 116, 117, 118, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 136, 137, 143, 144, 145, 146, 147, 148]
theorem soko4_2_closed_checked : check soko4_2.board soko4_2Support = true := by decide
theorem soko4_2_support_unique : soko4_2Support.Nodup := by decide
theorem soko4_2_initial_within : Within soko4_2Support soko4_2.initial := by decide
theorem soko4_2_every_trace_within {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko4_2.board soko4_2.initial directions final pushes moves) : Within soko4_2Support final :=
  trace_within (check_sound _ _ soko4_2_closed_checked) trace soko4_2_initial_within
end NetHack.Sokoban.ClosedComponents
