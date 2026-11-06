/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1120 (p : Pattern) (guard : d768 p = 1) : d302 p ≤ (0 : Int) + d189 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d302, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1119 p hg
    simpa only [d302, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d302, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1112 p hg
    simpa only [d302, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1121 (p : Pattern) (guard : d768 p = 1) : d303 p ≤ (0 : Int) + d190 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d303, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1117 p hg
    simpa only [d303, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d303, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1120 p hg
    simpa only [d303, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1122 (p : Pattern) (guard : d0 p = 1) : d304 p ≤ (0 : Int) + d191 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1123 (p : Pattern) (guard : d768 p = 1) : d305 p ≤ (0 : Int) + d191 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare237 p hg
    simpa only [d768, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1122 p hg
    simpa only [d768, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1124 (p : Pattern) (guard : d768 p = 1) : d306 p ≤ (0 : Int) + d192 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d306, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1123 p hg
    simpa only [d306, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d306, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1112 p hg
    simpa only [d306, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1125 (p : Pattern) (guard : d768 p = 1) : d307 p ≤ (0 : Int) + d193 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d307, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1124 p hg
    simpa only [d307, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d307, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1112 p hg
    simpa only [d307, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1126 (p : Pattern) (guard : d768 p = 1) : d308 p ≤ (0 : Int) + d194 p := by
  cases selected : p 132 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d308, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1121 p hg
    simpa only [d308, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d308, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1125 p hg
    simpa only [d308, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1127 (p : Pattern) (guard : d768 p = 1) : d309 p ≤ (0 : Int) + d195 p := by
  cases selected : p 108 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d309, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1114 p hg
    simpa only [d309, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d309, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1126 p hg
    simpa only [d309, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1128 (p : Pattern) (guard : d0 p = 1) : d267 p ≤ (0 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1129 (p : Pattern) (guard : d768 p = 1) : d268 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d268, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d768, d268, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d268, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d768, d268, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1130 (p : Pattern) (guard : d0 p = 1) : d278 p ≤ (0 : Int) + d237 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1131 (p : Pattern) (guard : d768 p = 1) : d279 p ≤ (0 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d279, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d768, d279, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d279, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d768, d279, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1132 (p : Pattern) (guard : d768 p = 1) : d280 p ≤ (0 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d280, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1129 p hg
    simpa only [d280, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d280, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d280, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1133 (p : Pattern) (guard : d0 p = 1) : d281 p ≤ (0 : Int) + d69 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1134 (p : Pattern) (guard : d768 p = 1) : d282 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d282, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare215 p hg
    simpa only [d768, d282, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d282, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d768, d282, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1135 (p : Pattern) (guard : d0 p = 1) : d283 p ≤ (0 : Int) + d240 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1136 (p : Pattern) (guard : d768 p = 1) : d284 p ≤ (0 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d284, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare218 p hg
    simpa only [d768, d284, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d284, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1135 p hg
    simpa only [d768, d284, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1137 (p : Pattern) (guard : d768 p = 1) : d285 p ≤ (0 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d285, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1134 p hg
    simpa only [d285, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d285, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d285, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1138 (p : Pattern) (guard : d768 p = 1) : d286 p ≤ (0 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d286, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d286, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d286, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1137 p hg
    simpa only [d286, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1139 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1140 (p : Pattern) (guard : d768 p = 1) : d287 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d287, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d768, d287, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d287, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1139 p hg
    simpa only [d768, d287, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1141 (p : Pattern) (guard : d768 p = 1) : d288 p ≤ (0 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d288, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1137 p hg
    simpa only [d288, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d288, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d288, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1142 (p : Pattern) (guard : d768 p = 1) : d289 p ≤ (0 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d289, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1138 p hg
    simpa only [d289, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d289, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1141 p hg
    simpa only [d289, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1143 (p : Pattern) (guard : d0 p = 1) : d295 p ≤ (0 : Int) + d246 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1144 (p : Pattern) (guard : d768 p = 1) : d296 p ≤ (0 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d296, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare228 p hg
    simpa only [d768, d296, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d296, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1143 p hg
    simpa only [d768, d296, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1145 (p : Pattern) (guard : d768 p = 1) : d297 p ≤ (0 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d297, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1144 p hg
    simpa only [d297, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d297, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d297, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1146 (p : Pattern) (guard : d0 p = 1) : d300 p ≤ (0 : Int) + d249 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1147 (p : Pattern) (guard : d768 p = 1) : d301 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d301, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d768, d301, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d301, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1146 p hg
    simpa only [d768, d301, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1148 (p : Pattern) (guard : d768 p = 1) : d302 p ≤ (0 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d302, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1147 p hg
    simpa only [d302, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d302, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d302, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1149 (p : Pattern) (guard : d768 p = 1) : d303 p ≤ (0 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d303, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1145 p hg
    simpa only [d303, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d303, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d303, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1150 (p : Pattern) (guard : d0 p = 1) : d304 p ≤ (0 : Int) + d253 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1151 (p : Pattern) (guard : d768 p = 1) : d305 p ≤ (0 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d305, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare237 p hg
    simpa only [d768, d305, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d305, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1150 p hg
    simpa only [d768, d305, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1152 (p : Pattern) (guard : d768 p = 1) : d306 p ≤ (0 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d306, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1151 p hg
    simpa only [d306, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d306, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d306, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1153 (p : Pattern) (guard : d768 p = 1) : d307 p ≤ (0 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d307, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1152 p hg
    simpa only [d307, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d307, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d307, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1154 (p : Pattern) (guard : d768 p = 1) : d308 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d308, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1149 p hg
    simpa only [d308, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d308, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1153 p hg
    simpa only [d308, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1155 (p : Pattern) (guard : d768 p = 1) : d309 p ≤ (0 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d309, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1142 p hg
    simpa only [d309, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d309, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1154 p hg
    simpa only [d309, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1156 (p : Pattern) (guard : d917 p = 1) : d0 p ≤ (0 : Int) + d0 p := by
  omega
theorem compare1157 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1158 (p : Pattern) (guard : d917 p = 1) : d6 p ≤ (0 : Int) + d2 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare283 p hg
    simpa only [d917, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1157 p hg
    simpa only [d917, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1159 (p : Pattern) (guard : d917 p = 1) : d7 p ≤ (0 : Int) + d919 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d7, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d7, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d7, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1158 p hg
    simpa only [d7, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1160 (p : Pattern) (guard : d917 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare1161 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (0 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1162 (p : Pattern) (guard : d917 p = 1) : d54 p ≤ (0 : Int) + d4 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare284 p hg
    simpa only [d917, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1161 p hg
    simpa only [d917, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1163 (p : Pattern) (guard : d917 p = 1) : d55 p ≤ (0 : Int) + d920 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d55, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1160 p hg
    simpa only [d55, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d55, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1162 p hg
    simpa only [d55, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1164 (p : Pattern) (guard : d917 p = 1) : d56 p ≤ (0 : Int) + d921 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d56, d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1159 p hg
    simpa only [d56, d921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d56, d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1163 p hg
    simpa only [d56, d921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1165 (p : Pattern) (guard : d917 p = 1) : d57 p ≤ (0 : Int) + d922 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d57, d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1159 p hg
    simpa only [d57, d922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d57, d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d57, d922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1166 (p : Pattern) (guard : d0 p = 1) : d267 p ≤ (0 : Int) + d928 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1167 (p : Pattern) (guard : d918 p = 1) : d268 p ≤ (0 : Int) + d929 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d918, d268, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1165 p hg
    simpa only [d918, d268, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d918, d268, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1166 p hg
    simpa only [d918, d268, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1168 (p : Pattern) (guard : d917 p = 1) : d106 p ≤ (0 : Int) + d930 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d106, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1159 p hg
    simpa only [d106, d930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d106, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1163 p hg
    simpa only [d106, d930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1169 (p : Pattern) (guard : d917 p = 1) : d119 p ≤ (0 : Int) + d931 p := by
  cases selected : p 187 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d119, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1159 p hg
    simpa only [d119, d931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d119, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1163 p hg
    simpa only [d119, d931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1170 (p : Pattern) (guard : d917 p = 1) : d120 p ≤ (0 : Int) + d932 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d120, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1159 p hg
    simpa only [d120, d932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d120, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1169 p hg
    simpa only [d120, d932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1171 (p : Pattern) (guard : d917 p = 1) : d121 p ≤ (0 : Int) + d933 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d121, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1170 p hg
    simpa only [d121, d933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d121, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1163 p hg
    simpa only [d121, d933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1172 (p : Pattern) (guard : d917 p = 1) : d122 p ≤ (0 : Int) + d934 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d122, d934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d122, d934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d122, d934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d122, d934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1173 (p : Pattern) (guard : d917 p = 1) : d179 p ≤ (0 : Int) + d935 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d179, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d179, d935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d179, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1172 p hg
    simpa only [d179, d935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1174 (p : Pattern) (guard : d0 p = 1) : d278 p ≤ (0 : Int) + d943 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1175 (p : Pattern) (guard : d918 p = 1) : d279 p ≤ (0 : Int) + d944 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d918, d279, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d918, d279, d944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d918, d279, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1174 p hg
    simpa only [d918, d279, d944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1176 (p : Pattern) (guard : d918 p = 1) : d280 p ≤ (0 : Int) + d945 p := by
  cases selected : p 134 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d280, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1167 p hg
    simpa only [d280, d945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d280, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1175 p hg
    simpa only [d280, d945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1177 (p : Pattern) (guard : d917 p = 1) : d68 p ≤ (0 : Int) + d946 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d68, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1165 p hg
    simpa only [d68, d946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d68, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1163 p hg
    simpa only [d68, d946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1178 (p : Pattern) (guard : d0 p = 1) : d281 p ≤ (0 : Int) + d947 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1179 (p : Pattern) (guard : d918 p = 1) : d282 p ≤ (0 : Int) + d948 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d918, d282, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1177 p hg
    simpa only [d918, d282, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d918, d282, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1178 p hg
    simpa only [d918, d282, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1180 (p : Pattern) (guard : d917 p = 1) : d181 p ≤ (0 : Int) + d949 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d181, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1172 p hg
    simpa only [d181, d949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d181, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1163 p hg
    simpa only [d181, d949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1181 (p : Pattern) (guard : d0 p = 1) : d283 p ≤ (0 : Int) + d950 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1182 (p : Pattern) (guard : d918 p = 1) : d284 p ≤ (0 : Int) + d951 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d918, d284, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1180 p hg
    simpa only [d918, d284, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d918, d284, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d918, d284, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1183 (p : Pattern) (guard : d918 p = 1) : d285 p ≤ (0 : Int) + d952 p := by
  cases selected : p 134 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d285, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1179 p hg
    simpa only [d285, d952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d285, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1182 p hg
    simpa only [d285, d952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1184 (p : Pattern) (guard : d918 p = 1) : d286 p ≤ (0 : Int) + d953 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d286, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1176 p hg
    simpa only [d286, d953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d286, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1183 p hg
    simpa only [d286, d953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1185 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (0 : Int) + d936 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1186 (p : Pattern) (guard : d918 p = 1) : d287 p ≤ (0 : Int) + d954 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d918, d287, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1163 p hg
    simpa only [d918, d287, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d918, d287, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1185 p hg
    simpa only [d918, d287, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1187 (p : Pattern) (guard : d918 p = 1) : d288 p ≤ (0 : Int) + d955 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d288, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1183 p hg
    simpa only [d288, d955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d288, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1186 p hg
    simpa only [d288, d955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1188 (p : Pattern) (guard : d918 p = 1) : d289 p ≤ (0 : Int) + d956 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d289, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1184 p hg
    simpa only [d289, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d289, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1187 p hg
    simpa only [d289, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1189 (p : Pattern) (guard : d917 p = 1) : d137 p ≤ (0 : Int) + d957 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d137, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1169 p hg
    simpa only [d137, d957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d137, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1163 p hg
    simpa only [d137, d957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1190 (p : Pattern) (guard : d917 p = 1) : d139 p ≤ (0 : Int) + d958 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d139, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1170 p hg
    simpa only [d139, d958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d139, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1189 p hg
    simpa only [d139, d958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1191 (p : Pattern) (guard : d917 p = 1) : d153 p ≤ (0 : Int) + d959 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d153, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1165 p hg
    simpa only [d153, d959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d153, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1190 p hg
    simpa only [d153, d959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1192 (p : Pattern) (guard : d917 p = 1) : d186 p ≤ (0 : Int) + d960 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d186, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1165 p hg
    simpa only [d186, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d186, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1191 p hg
    simpa only [d186, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1193 (p : Pattern) (guard : d0 p = 1) : d295 p ≤ (0 : Int) + d965 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1194 (p : Pattern) (guard : d918 p = 1) : d296 p ≤ (0 : Int) + d966 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d918, d296, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1192 p hg
    simpa only [d918, d296, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d918, d296, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1193 p hg
    simpa only [d918, d296, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1195 (p : Pattern) (guard : d918 p = 1) : d297 p ≤ (0 : Int) + d967 p := by
  cases selected : p 134 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d297, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1194 p hg
    simpa only [d297, d967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d297, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1186 p hg
    simpa only [d297, d967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1196 (p : Pattern) (guard : d917 p = 1) : d138 p ≤ (0 : Int) + d968 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d138, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1159 p hg
    simpa only [d138, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d138, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1189 p hg
    simpa only [d138, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1197 (p : Pattern) (guard : d917 p = 1) : d140 p ≤ (0 : Int) + d969 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d140, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1196 p hg
    simpa only [d140, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d140, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1190 p hg
    simpa only [d140, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1198 (p : Pattern) (guard : d917 p = 1) : d188 p ≤ (0 : Int) + d970 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d188, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1197 p hg
    simpa only [d188, d970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d188, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1163 p hg
    simpa only [d188, d970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1199 (p : Pattern) (guard : d0 p = 1) : d300 p ≤ (0 : Int) + d973 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1200 (p : Pattern) (guard : d918 p = 1) : d301 p ≤ (0 : Int) + d974 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d918, d301, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1198 p hg
    simpa only [d918, d301, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d918, d301, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1199 p hg
    simpa only [d918, d301, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1201 (p : Pattern) (guard : d918 p = 1) : d302 p ≤ (0 : Int) + d975 p := by
  cases selected : p 134 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d302, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1200 p hg
    simpa only [d302, d975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d302, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1186 p hg
    simpa only [d302, d975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1202 (p : Pattern) (guard : d918 p = 1) : d303 p ≤ (0 : Int) + d976 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d303, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1195 p hg
    simpa only [d303, d976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d303, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1201 p hg
    simpa only [d303, d976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1203 (p : Pattern) (guard : d917 p = 1) : d191 p ≤ (0 : Int) + d977 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d191, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1191 p hg
    simpa only [d191, d977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d191, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1163 p hg
    simpa only [d191, d977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1204 (p : Pattern) (guard : d0 p = 1) : d304 p ≤ (0 : Int) + d978 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1205 (p : Pattern) (guard : d918 p = 1) : d305 p ≤ (0 : Int) + d979 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d918, d305, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1203 p hg
    simpa only [d918, d305, d979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d918, d305, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1204 p hg
    simpa only [d918, d305, d979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1206 (p : Pattern) (guard : d918 p = 1) : d306 p ≤ (0 : Int) + d980 p := by
  cases selected : p 134 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d306, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1205 p hg
    simpa only [d306, d980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d306, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1186 p hg
    simpa only [d306, d980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1207 (p : Pattern) (guard : d918 p = 1) : d307 p ≤ (0 : Int) + d981 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d307, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1206 p hg
    simpa only [d307, d981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d307, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1186 p hg
    simpa only [d307, d981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1208 (p : Pattern) (guard : d918 p = 1) : d308 p ≤ (0 : Int) + d982 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d308, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1202 p hg
    simpa only [d308, d982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d308, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d308, d982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1209 (p : Pattern) (guard : d918 p = 1) : d309 p ≤ (0 : Int) + d983 p := by
  cases selected : p 108 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d309, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1188 p hg
    simpa only [d309, d983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d309, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1208 p hg
    simpa only [d309, d983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1210 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (1 : Int) + d57 p := by
  omega
theorem compare1211 (p : Pattern) (guard : d0 p = 1) : d267 p ≤ (1 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1212 (p : Pattern) (guard : d768 p = 1) : d268 p ≤ (1 : Int) + d57 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1210 p hg
    simpa only [d768, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1211 p hg
    simpa only [d768, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1213 (p : Pattern) (guard : d1 p = 1) : d179 p ≤ (1 : Int) + d179 p := by
  omega
theorem compare1214 (p : Pattern) (guard : d0 p = 1) : d278 p ≤ (1 : Int) + d179 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1215 (p : Pattern) (guard : d768 p = 1) : d279 p ≤ (1 : Int) + d179 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1213 p hg
    simpa only [d768, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1214 p hg
    simpa only [d768, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1216 (p : Pattern) (guard : d768 p = 1) : d280 p ≤ (1 : Int) + d180 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d280, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d280, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d280, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1215 p hg
    simpa only [d280, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1217 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (1 : Int) + d68 p := by
  omega
theorem compare1218 (p : Pattern) (guard : d0 p = 1) : d281 p ≤ (1 : Int) + d68 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1219 (p : Pattern) (guard : d768 p = 1) : d282 p ≤ (1 : Int) + d68 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1217 p hg
    simpa only [d768, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d768, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1220 (p : Pattern) (guard : d1 p = 1) : d181 p ≤ (1 : Int) + d181 p := by
  omega
theorem compare1221 (p : Pattern) (guard : d0 p = 1) : d283 p ≤ (1 : Int) + d181 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1222 (p : Pattern) (guard : d768 p = 1) : d284 p ≤ (1 : Int) + d181 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1220 p hg
    simpa only [d768, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1221 p hg
    simpa only [d768, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1223 (p : Pattern) (guard : d768 p = 1) : d285 p ≤ (1 : Int) + d182 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d285, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1219 p hg
    simpa only [d285, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d285, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1222 p hg
    simpa only [d285, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1224 (p : Pattern) (guard : d768 p = 1) : d286 p ≤ (1 : Int) + d183 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d286, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1216 p hg
    simpa only [d286, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d286, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1223 p hg
    simpa only [d286, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1225 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (1 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1226 (p : Pattern) (guard : d768 p = 1) : d287 p ≤ (1 : Int) + d55 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1025 p hg
    simpa only [d768, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1225 p hg
    simpa only [d768, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1227 (p : Pattern) (guard : d768 p = 1) : d288 p ≤ (1 : Int) + d184 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d288, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1223 p hg
    simpa only [d288, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d288, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1226 p hg
    simpa only [d288, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1228 (p : Pattern) (guard : d768 p = 1) : d289 p ≤ (1 : Int) + d185 p := by
  cases selected : p 132 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d289, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1224 p hg
    simpa only [d289, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d289, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1227 p hg
    simpa only [d289, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1229 (p : Pattern) (guard : d1 p = 1) : d186 p ≤ (1 : Int) + d186 p := by
  omega
theorem compare1230 (p : Pattern) (guard : d0 p = 1) : d295 p ≤ (1 : Int) + d186 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1231 (p : Pattern) (guard : d768 p = 1) : d296 p ≤ (1 : Int) + d186 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1229 p hg
    simpa only [d768, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1230 p hg
    simpa only [d768, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1232 (p : Pattern) (guard : d768 p = 1) : d297 p ≤ (1 : Int) + d187 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d297, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1231 p hg
    simpa only [d297, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d297, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1226 p hg
    simpa only [d297, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1233 (p : Pattern) (guard : d1 p = 1) : d188 p ≤ (1 : Int) + d188 p := by
  omega
theorem compare1234 (p : Pattern) (guard : d0 p = 1) : d300 p ≤ (1 : Int) + d188 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1235 (p : Pattern) (guard : d768 p = 1) : d301 p ≤ (1 : Int) + d188 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1233 p hg
    simpa only [d768, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1234 p hg
    simpa only [d768, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1236 (p : Pattern) (guard : d768 p = 1) : d302 p ≤ (1 : Int) + d189 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d302, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1235 p hg
    simpa only [d302, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d302, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1226 p hg
    simpa only [d302, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1237 (p : Pattern) (guard : d768 p = 1) : d303 p ≤ (1 : Int) + d190 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d303, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1232 p hg
    simpa only [d303, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d303, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1236 p hg
    simpa only [d303, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1238 (p : Pattern) (guard : d1 p = 1) : d191 p ≤ (1 : Int) + d191 p := by
  omega
theorem compare1239 (p : Pattern) (guard : d0 p = 1) : d304 p ≤ (1 : Int) + d191 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1240 (p : Pattern) (guard : d768 p = 1) : d305 p ≤ (1 : Int) + d191 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1238 p hg
    simpa only [d768, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1239 p hg
    simpa only [d768, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1241 (p : Pattern) (guard : d768 p = 1) : d306 p ≤ (1 : Int) + d192 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d306, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1240 p hg
    simpa only [d306, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d306, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1226 p hg
    simpa only [d306, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1242 (p : Pattern) (guard : d768 p = 1) : d307 p ≤ (1 : Int) + d193 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d307, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1241 p hg
    simpa only [d307, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d307, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1226 p hg
    simpa only [d307, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1243 (p : Pattern) (guard : d768 p = 1) : d308 p ≤ (1 : Int) + d194 p := by
  cases selected : p 132 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d308, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1237 p hg
    simpa only [d308, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d308, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1242 p hg
    simpa only [d308, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1244 (p : Pattern) (guard : d768 p = 1) : d309 p ≤ (1 : Int) + d195 p := by
  cases selected : p 108 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d309, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1228 p hg
    simpa only [d309, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d309, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1243 p hg
    simpa only [d309, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1245 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1246 (p : Pattern) (guard : d770 p = 1) : d7 p ≤ (0 : Int) + d21 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d770, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1245 p hg
    simpa only [d770, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1247 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (0 : Int) + d56 p := by
  omega
theorem compare1248 (p : Pattern) (guard : d0 p = 1) : d56 p ≤ (0 : Int) + d261 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1249 (p : Pattern) (guard : d770 p = 1) : d56 p ≤ (0 : Int) + d375 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d770, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1248 p hg
    simpa only [d770, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1250 (p : Pattern) (guard : d770 p = 1) : d57 p ≤ (0 : Int) + d376 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d57, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d57, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d57, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1249 p hg
    simpa only [d57, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1251 (p : Pattern) (guard : d0 p = 1) : d267 p ≤ (0 : Int) + d378 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1252 (p : Pattern) (guard : d984 p = 1) : d268 p ≤ (0 : Int) + d379 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d984, d268, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1250 p hg
    simpa only [d984, d268, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d268, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1251 p hg
    simpa only [d984, d268, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1253 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d260 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1254 (p : Pattern) (guard : d770 p = 1) : d55 p ≤ (0 : Int) + d380 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d770, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1253 p hg
    simpa only [d770, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1255 (p : Pattern) (guard : d770 p = 1) : d106 p ≤ (0 : Int) + d381 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d106, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d106, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d106, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1254 p hg
    simpa only [d106, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1256 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (0 : Int) + d120 p := by
  omega
theorem compare1257 (p : Pattern) (guard : d0 p = 1) : d120 p ≤ (0 : Int) + d272 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1258 (p : Pattern) (guard : d770 p = 1) : d120 p ≤ (0 : Int) + d382 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1256 p hg
    simpa only [d770, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1257 p hg
    simpa only [d770, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1259 (p : Pattern) (guard : d770 p = 1) : d121 p ≤ (0 : Int) + d383 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d121, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1258 p hg
    simpa only [d121, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d121, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1254 p hg
    simpa only [d121, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
