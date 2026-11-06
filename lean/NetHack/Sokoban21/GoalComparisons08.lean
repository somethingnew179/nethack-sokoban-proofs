/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.GoalComparisons07
import NetHack.Sokoban21.Comparisons167
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem goalC1040 (pattern : Twelve) (guard : d3256 pattern = 1) : d1154 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1036 pattern childGuard
    simpa only [d3256, d1154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1039 pattern childGuard
    simpa only [d3256, d1154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1041 (pattern : Twelve) (guard : d0 pattern = 1) : d1122 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1042 (pattern : Twelve) (guard : d3255 pattern = 1) : d1138 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC525 pattern childGuard
    simpa only [d3255, d1138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1041 pattern childGuard
    simpa only [d3255, d1138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1043 (pattern : Twelve) (guard : d0 pattern = 1) : d1135 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1044 (pattern : Twelve) (guard : d3259 pattern = 1) : d1155 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1042 pattern childGuard
    simpa only [d3259, d1155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1043 pattern childGuard
    simpa only [d3259, d1155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1045 (pattern : Twelve) (guard : d3260 pattern = 1) : d1165 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1165, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1040 pattern childGuard
    simpa only [d3260, d1165, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1165, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1044 pattern childGuard
    simpa only [d3260, d1165, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1046 (pattern : Twelve) (guard : d3261 pattern = 1) : d1173 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d1173, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1033 pattern childGuard
    simpa only [d3261, d1173, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d1173, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1045 pattern childGuard
    simpa only [d3261, d1173, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1047 (pattern : Twelve) (guard : d0 pattern = 1) : d1111 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1048 (pattern : Twelve) (guard : d3251 pattern = 1) : d1124 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC544 pattern childGuard
    simpa only [d3251, d1124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1047 pattern childGuard
    simpa only [d3251, d1124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1049 (pattern : Twelve) (guard : d3252 pattern = 1) : d1139 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC545 pattern childGuard
    simpa only [d3252, d1139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1048 pattern childGuard
    simpa only [d3252, d1139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1050 (pattern : Twelve) (guard : d0 pattern = 1) : d509 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1051 (pattern : Twelve) (guard : d3251 pattern = 1) : d509 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC544 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1050 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1052 (pattern : Twelve) (guard : d0 pattern = 1) : d1120 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1053 (pattern : Twelve) (guard : d3255 pattern = 1) : d1140 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1051 pattern childGuard
    simpa only [d3255, d1140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1052 pattern childGuard
    simpa only [d3255, d1140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1054 (pattern : Twelve) (guard : d3256 pattern = 1) : d1156 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1049 pattern childGuard
    simpa only [d3256, d1156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1053 pattern childGuard
    simpa only [d3256, d1156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1055 (pattern : Twelve) (guard : d0 pattern = 1) : d1125 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1056 (pattern : Twelve) (guard : d3255 pattern = 1) : d1141 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC558 pattern childGuard
    simpa only [d3255, d1141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1055 pattern childGuard
    simpa only [d3255, d1141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1057 (pattern : Twelve) (guard : d0 pattern = 1) : d1142 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1058 (pattern : Twelve) (guard : d3259 pattern = 1) : d1157 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1056 pattern childGuard
    simpa only [d3259, d1157, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1057 pattern childGuard
    simpa only [d3259, d1157, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1059 (pattern : Twelve) (guard : d3260 pattern = 1) : d1166 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1166, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1054 pattern childGuard
    simpa only [d3260, d1166, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1166, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1058 pattern childGuard
    simpa only [d3260, d1166, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1060 (pattern : Twelve) (guard : d0 pattern = 1) : d1122 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1061 (pattern : Twelve) (guard : d3255 pattern = 1) : d1138 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC574 pattern childGuard
    simpa only [d3255, d1138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1060 pattern childGuard
    simpa only [d3255, d1138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1062 (pattern : Twelve) (guard : d0 pattern = 1) : d1135 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1063 (pattern : Twelve) (guard : d3259 pattern = 1) : d1155 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1061 pattern childGuard
    simpa only [d3259, d1155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1062 pattern childGuard
    simpa only [d3259, d1155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1064 (pattern : Twelve) (guard : d3263 pattern = 1) : d1167 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1167, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1063 pattern childGuard
    simpa only [d3263, d1167, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1167, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3263, d1167, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1065 (pattern : Twelve) (guard : d3264 pattern = 1) : d1174 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d1174, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1059 pattern childGuard
    simpa only [d3264, d1174, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d1174, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1064 pattern childGuard
    simpa only [d3264, d1174, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1066 (pattern : Twelve) (guard : d3265 pattern = 1) : d1177 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3265, d1177, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1046 pattern childGuard
    simpa only [d3265, d1177, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3265, d1177, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1065 pattern childGuard
    simpa only [d3265, d1177, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1067 (pattern : Twelve) (guard : d3268 pattern = 1) : d1178 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1178 pattern).2
  change d1178 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1068 (pattern : Twelve) (guard : d3269 pattern = 1) : d1180 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3269, d1180, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1066 pattern childGuard
    simpa only [d3269, d1180, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3269, d1180, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1067 pattern childGuard
    simpa only [d3269, d1180, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1069 (pattern : Twelve) (guard : d3272 pattern = 1) : d1178 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1178 pattern).2
  change d1178 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1070 (pattern : Twelve) (guard : d3273 pattern = 1) : d1181 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3273, d1181, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1068 pattern childGuard
    simpa only [d3273, d1181, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3273, d1181, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1069 pattern childGuard
    simpa only [d3273, d1181, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1071 (pattern : Twelve) (guard : d3276 pattern = 1) : d1179 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1179 pattern).2
  change d1179 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1072 (pattern : Twelve) (guard : d3277 pattern = 1) : d1182 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3277, d1182, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1070 pattern childGuard
    simpa only [d3277, d1182, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3277, d1182, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1071 pattern childGuard
    simpa only [d3277, d1182, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1073 (pattern : Twelve) (guard : d3247 pattern = 1) : d1183 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d1183, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC603 pattern childGuard
    simpa only [d3247, d1183, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d1183, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6985 pattern childGuard
    simpa only [d3247, d1183, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1074 (pattern : Twelve) (guard : d3248 pattern = 1) : d1189 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC593 pattern childGuard
    simpa only [d3248, d1189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1073 pattern childGuard
    simpa only [d3248, d1189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1075 (pattern : Twelve) (guard : d3249 pattern = 1) : d1199 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC599 pattern childGuard
    simpa only [d3249, d1199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1074 pattern childGuard
    simpa only [d3249, d1199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1076 (pattern : Twelve) (guard : d3247 pattern = 1) : d158 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC596 pattern childGuard
    simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1077 (pattern : Twelve) (guard : d3248 pattern = 1) : d1190 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC598 pattern childGuard
    simpa only [d3248, d1190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1076 pattern childGuard
    simpa only [d3248, d1190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1078 (pattern : Twelve) (guard : d0 pattern = 1) : d644 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1079 (pattern : Twelve) (guard : d3247 pattern = 1) : d1184 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d1184, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC603 pattern childGuard
    simpa only [d3247, d1184, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d1184, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1078 pattern childGuard
    simpa only [d3247, d1184, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1080 (pattern : Twelve) (guard : d0 pattern = 1) : d670 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1081 (pattern : Twelve) (guard : d3251 pattern = 1) : d1191 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1079 pattern childGuard
    simpa only [d3251, d1191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1080 pattern childGuard
    simpa only [d3251, d1191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1082 (pattern : Twelve) (guard : d3252 pattern = 1) : d1200 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1077 pattern childGuard
    simpa only [d3252, d1200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1081 pattern childGuard
    simpa only [d3252, d1200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1083 (pattern : Twelve) (guard : d3253 pattern = 1) : d1216 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1075 pattern childGuard
    simpa only [d3253, d1216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1082 pattern childGuard
    simpa only [d3253, d1216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1084 (pattern : Twelve) (guard : d3247 pattern = 1) : d663 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d663, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC621 pattern childGuard
    simpa only [d3247, d663, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d663, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d3247, d663, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1085 (pattern : Twelve) (guard : d3248 pattern = 1) : d1192 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC619 pattern childGuard
    simpa only [d3248, d1192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1084 pattern childGuard
    simpa only [d3248, d1192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1086 (pattern : Twelve) (guard : d3252 pattern = 1) : d1201 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1085 pattern childGuard
    simpa only [d3252, d1201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC629 pattern childGuard
    simpa only [d3252, d1201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1087 (pattern : Twelve) (guard : d0 pattern = 1) : d663 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1088 (pattern : Twelve) (guard : d3251 pattern = 1) : d692 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC627 pattern childGuard
    simpa only [d3251, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1087 pattern childGuard
    simpa only [d3251, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1089 (pattern : Twelve) (guard : d0 pattern = 1) : d1191 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1090 (pattern : Twelve) (guard : d3255 pattern = 1) : d1202 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1088 pattern childGuard
    simpa only [d3255, d1202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1089 pattern childGuard
    simpa only [d3255, d1202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1091 (pattern : Twelve) (guard : d3256 pattern = 1) : d1217 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1086 pattern childGuard
    simpa only [d3256, d1217, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1090 pattern childGuard
    simpa only [d3256, d1217, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1092 (pattern : Twelve) (guard : d3257 pattern = 1) : d1228 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d1228, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1083 pattern childGuard
    simpa only [d3257, d1228, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d1228, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1091 pattern childGuard
    simpa only [d3257, d1228, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1093 (pattern : Twelve) (guard : d0 pattern = 1) : d1183 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1094 (pattern : Twelve) (guard : d3251 pattern = 1) : d1193 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC645 pattern childGuard
    simpa only [d3251, d1193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1093 pattern childGuard
    simpa only [d3251, d1193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1095 (pattern : Twelve) (guard : d3252 pattern = 1) : d1203 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC649 pattern childGuard
    simpa only [d3252, d1203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1094 pattern childGuard
    simpa only [d3252, d1203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1096 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1097 (pattern : Twelve) (guard : d3251 pattern = 1) : d158 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC648 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1096 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1098 (pattern : Twelve) (guard : d3255 pattern = 1) : d1204 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1097 pattern childGuard
    simpa only [d3255, d1204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1089 pattern childGuard
    simpa only [d3255, d1204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1099 (pattern : Twelve) (guard : d3256 pattern = 1) : d1218 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1095 pattern childGuard
    simpa only [d3256, d1218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1098 pattern childGuard
    simpa only [d3256, d1218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1100 (pattern : Twelve) (guard : d0 pattern = 1) : d1202 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1101 (pattern : Twelve) (guard : d3259 pattern = 1) : d1219 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC668 pattern childGuard
    simpa only [d3259, d1219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1100 pattern childGuard
    simpa only [d3259, d1219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1102 (pattern : Twelve) (guard : d3260 pattern = 1) : d1229 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1229, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1099 pattern childGuard
    simpa only [d3260, d1229, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1229, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1101 pattern childGuard
    simpa only [d3260, d1229, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1103 (pattern : Twelve) (guard : d3261 pattern = 1) : d1237 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d1237, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1092 pattern childGuard
    simpa only [d3261, d1237, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d1237, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1102 pattern childGuard
    simpa only [d3261, d1237, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1104 (pattern : Twelve) (guard : d0 pattern = 1) : d1185 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1105 (pattern : Twelve) (guard : d3251 pattern = 1) : d1194 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC683 pattern childGuard
    simpa only [d3251, d1194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1104 pattern childGuard
    simpa only [d3251, d1194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1106 (pattern : Twelve) (guard : d3252 pattern = 1) : d1205 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC684 pattern childGuard
    simpa only [d3252, d1205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1105 pattern childGuard
    simpa only [d3252, d1205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1107 (pattern : Twelve) (guard : d0 pattern = 1) : d657 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1108 (pattern : Twelve) (guard : d3251 pattern = 1) : d657 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC683 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1107 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1109 (pattern : Twelve) (guard : d0 pattern = 1) : d1191 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1110 (pattern : Twelve) (guard : d3255 pattern = 1) : d1206 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1108 pattern childGuard
    simpa only [d3255, d1206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1109 pattern childGuard
    simpa only [d3255, d1206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1111 (pattern : Twelve) (guard : d3256 pattern = 1) : d1220 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1106 pattern childGuard
    simpa only [d3256, d1220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1110 pattern childGuard
    simpa only [d3256, d1220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1112 (pattern : Twelve) (guard : d0 pattern = 1) : d1207 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1113 (pattern : Twelve) (guard : d3259 pattern = 1) : d1221 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC700 pattern childGuard
    simpa only [d3259, d1221, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1112 pattern childGuard
    simpa only [d3259, d1221, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1114 (pattern : Twelve) (guard : d3260 pattern = 1) : d1230 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1230, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1111 pattern childGuard
    simpa only [d3260, d1230, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1230, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1113 pattern childGuard
    simpa only [d3260, d1230, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1115 (pattern : Twelve) (guard : d0 pattern = 1) : d1202 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1116 (pattern : Twelve) (guard : d3259 pattern = 1) : d1219 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC717 pattern childGuard
    simpa only [d3259, d1219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1115 pattern childGuard
    simpa only [d3259, d1219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1117 (pattern : Twelve) (guard : d3263 pattern = 1) : d1231 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1231, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1116 pattern childGuard
    simpa only [d3263, d1231, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1231, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3263, d1231, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1118 (pattern : Twelve) (guard : d3264 pattern = 1) : d1238 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d1238, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1114 pattern childGuard
    simpa only [d3264, d1238, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d1238, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1117 pattern childGuard
    simpa only [d3264, d1238, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1119 (pattern : Twelve) (guard : d3265 pattern = 1) : d1241 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3265, d1241, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1103 pattern childGuard
    simpa only [d3265, d1241, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3265, d1241, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1118 pattern childGuard
    simpa only [d3265, d1241, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1120 (pattern : Twelve) (guard : d3268 pattern = 1) : d1242 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1242 pattern).2
  change d1242 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1121 (pattern : Twelve) (guard : d3269 pattern = 1) : d1244 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3269, d1244, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1119 pattern childGuard
    simpa only [d3269, d1244, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3269, d1244, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1120 pattern childGuard
    simpa only [d3269, d1244, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1122 (pattern : Twelve) (guard : d3272 pattern = 1) : d1242 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1242 pattern).2
  change d1242 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1123 (pattern : Twelve) (guard : d3273 pattern = 1) : d1245 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3273, d1245, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1121 pattern childGuard
    simpa only [d3273, d1245, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3273, d1245, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1122 pattern childGuard
    simpa only [d3273, d1245, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1124 (pattern : Twelve) (guard : d3276 pattern = 1) : d1243 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1243 pattern).2
  change d1243 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1125 (pattern : Twelve) (guard : d3277 pattern = 1) : d1246 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3277, d1246, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1123 pattern childGuard
    simpa only [d3277, d1246, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3277, d1246, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1124 pattern childGuard
    simpa only [d3277, d1246, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1126 (pattern : Twelve) (guard : d3276 pattern = 1) : d1266 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1266 pattern).2
  change d1266 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1127 (pattern : Twelve) (guard : d3277 pattern = 1) : d1267 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3277, d1267, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC803 pattern childGuard
    simpa only [d3277, d1267, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3277, d1267, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1126 pattern childGuard
    simpa only [d3277, d1267, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1128 (pattern : Twelve) (guard : d3269 pattern = 1) : d1268 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3269, d1268, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC799 pattern childGuard
    simpa only [d3269, d1268, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3269, d1268, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC829 pattern childGuard
    simpa only [d3269, d1268, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1129 (pattern : Twelve) (guard : d3272 pattern = 1) : d1268 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1268 pattern).2
  change d1268 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1130 (pattern : Twelve) (guard : d3273 pattern = 1) : d1268 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3273, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1128 pattern childGuard
    simpa only [d3273, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3273, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1129 pattern childGuard
    simpa only [d3273, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1131 (pattern : Twelve) (guard : d3276 pattern = 1) : d1269 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1269 pattern).2
  change d1269 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1132 (pattern : Twelve) (guard : d3277 pattern = 1) : d1270 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3277, d1270, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1130 pattern childGuard
    simpa only [d3277, d1270, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3277, d1270, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1131 pattern childGuard
    simpa only [d3277, d1270, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1133 (pattern : Twelve) (guard : d3273 pattern = 1) : d1271 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3273, d1271, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC801 pattern childGuard
    simpa only [d3273, d1271, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3273, d1271, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC831 pattern childGuard
    simpa only [d3273, d1271, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1134 (pattern : Twelve) (guard : d3276 pattern = 1) : d1272 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1272 pattern).2
  change d1272 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1135 (pattern : Twelve) (guard : d3277 pattern = 1) : d1273 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3277, d1273, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1133 pattern childGuard
    simpa only [d3277, d1273, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3277, d1273, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1134 pattern childGuard
    simpa only [d3277, d1273, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1136 (pattern : Twelve) (guard : d3277 pattern = 1) : d1274 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3277, d1274, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC803 pattern childGuard
    simpa only [d3277, d1274, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3277, d1274, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC833 pattern childGuard
    simpa only [d3277, d1274, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1137 (pattern : Twelve) (guard : d0 pattern = 1) : d8 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1138 (pattern : Twelve) (guard : d1867 pattern = 1) : d1275 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7730 pattern childGuard
    simpa only [d1867, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1137 pattern childGuard
    simpa only [d1867, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1139 (pattern : Twelve) (guard : d3247 pattern = 1) : d1278 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d1278, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1138 pattern childGuard
    simpa only [d3247, d1278, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d1278, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9409 pattern childGuard
    simpa only [d3247, d1278, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1140 (pattern : Twelve) (guard : d0 pattern = 1) : d872 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1141 (pattern : Twelve) (guard : d3251 pattern = 1) : d1284 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1139 pattern childGuard
    simpa only [d3251, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1140 pattern childGuard
    simpa only [d3251, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1142 (pattern : Twelve) (guard : d3252 pattern = 1) : d1293 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC748 pattern childGuard
    simpa only [d3252, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1141 pattern childGuard
    simpa only [d3252, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1143 (pattern : Twelve) (guard : d0 pattern = 1) : d19 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1144 (pattern : Twelve) (guard : d3247 pattern = 1) : d19 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC19 pattern childGuard
    simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1143 pattern childGuard
    simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1145 (pattern : Twelve) (guard : d0 pattern = 1) : d19 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1146 (pattern : Twelve) (guard : d3251 pattern = 1) : d19 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1144 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1145 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1147 (pattern : Twelve) (guard : d3255 pattern = 1) : d1294 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1146 pattern childGuard
    simpa only [d3255, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC812 pattern childGuard
    simpa only [d3255, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1148 (pattern : Twelve) (guard : d3256 pattern = 1) : d1305 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1142 pattern childGuard
    simpa only [d3256, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1147 pattern childGuard
    simpa only [d3256, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1149 (pattern : Twelve) (guard : d0 pattern = 1) : d1285 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1150 (pattern : Twelve) (guard : d3255 pattern = 1) : d1295 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC760 pattern childGuard
    simpa only [d3255, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1149 pattern childGuard
    simpa only [d3255, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1151 (pattern : Twelve) (guard : d0 pattern = 1) : d1296 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1152 (pattern : Twelve) (guard : d3259 pattern = 1) : d1306 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1150 pattern childGuard
    simpa only [d3259, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1151 pattern childGuard
    simpa only [d3259, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1153 (pattern : Twelve) (guard : d3260 pattern = 1) : d1313 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1313, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1148 pattern childGuard
    simpa only [d3260, d1313, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1313, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1152 pattern childGuard
    simpa only [d3260, d1313, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1154 (pattern : Twelve) (guard : d0 pattern = 1) : d1284 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1155 (pattern : Twelve) (guard : d3255 pattern = 1) : d1293 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC771 pattern childGuard
    simpa only [d3255, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1154 pattern childGuard
    simpa only [d3255, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1156 (pattern : Twelve) (guard : d0 pattern = 1) : d1294 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1157 (pattern : Twelve) (guard : d3259 pattern = 1) : d1305 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1155 pattern childGuard
    simpa only [d3259, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1156 pattern childGuard
    simpa only [d3259, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1158 (pattern : Twelve) (guard : d0 pattern = 1) : d1306 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1159 (pattern : Twelve) (guard : d3263 pattern = 1) : d1313 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1313, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1157 pattern childGuard
    simpa only [d3263, d1313, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1313, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1158 pattern childGuard
    simpa only [d3263, d1313, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1160 (pattern : Twelve) (guard : d3264 pattern = 1) : d1313 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1153 pattern childGuard
    simpa only [d3264, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1159 pattern childGuard
    simpa only [d3264, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1161 (pattern : Twelve) (guard : d0 pattern = 1) : d1287 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1162 (pattern : Twelve) (guard : d3255 pattern = 1) : d1297 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC784 pattern childGuard
    simpa only [d3255, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1161 pattern childGuard
    simpa only [d3255, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1163 (pattern : Twelve) (guard : d0 pattern = 1) : d1298 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1164 (pattern : Twelve) (guard : d3259 pattern = 1) : d1307 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1162 pattern childGuard
    simpa only [d3259, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1163 pattern childGuard
    simpa only [d3259, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1165 (pattern : Twelve) (guard : d0 pattern = 1) : d1308 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1166 (pattern : Twelve) (guard : d3263 pattern = 1) : d1314 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1314, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1164 pattern childGuard
    simpa only [d3263, d1314, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1314, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1165 pattern childGuard
    simpa only [d3263, d1314, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1167 (pattern : Twelve) (guard : d0 pattern = 1) : d1315 pattern ≤ (0 : Int) + d3287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1168 (pattern : Twelve) (guard : d3267 pattern = 1) : d1319 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d1319, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1166 pattern childGuard
    simpa only [d3267, d1319, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d1319, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1167 pattern childGuard
    simpa only [d3267, d1319, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1169 (pattern : Twelve) (guard : d3268 pattern = 1) : d1321 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3268, d1321, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1160 pattern childGuard
    simpa only [d3268, d1321, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3268, d1321, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1168 pattern childGuard
    simpa only [d3268, d1321, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
