/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons350
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare49140 (p : Pattern) (guard : d8131 p = 1) : d1191 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1191, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49135 p hg
    simpa only [d8131, d1191, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1191, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49139 p hg
    simpa only [d8131, d1191, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49141 (p : Pattern) (guard : d8118 p = 1) : d1202 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1202, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35400 p hg
    simpa only [d8118, d1202, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1202, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d1202, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49142 (p : Pattern) (guard : d8124 p = 1) : d1203 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1203, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49141 p hg
    simpa only [d8124, d1203, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1203, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38245 p hg
    simpa only [d8124, d1203, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49143 (p : Pattern) (guard : d8130 p = 1) : d1204 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1204, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49142 p hg
    simpa only [d8130, d1204, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1204, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38247 p hg
    simpa only [d8130, d1204, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49144 (p : Pattern) (guard : d8136 p = 1) : d1205 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1205, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49143 p hg
    simpa only [d8136, d1205, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1205, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41444 p hg
    simpa only [d8136, d1205, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49145 (p : Pattern) (guard : d8137 p = 1) : d1258 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1258, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49140 p hg
    simpa only [d8137, d1258, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1258, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d8137, d1258, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49146 (p : Pattern) (guard : d8138 p = 1) : d1259 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1259, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49130 p hg
    simpa only [d8138, d1259, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1259, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49145 p hg
    simpa only [d8138, d1259, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49147 (p : Pattern) (guard : d8107 p = 1) : d1152 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1152, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35390 p hg
    simpa only [d8107, d1152, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1152, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49057 p hg
    simpa only [d8107, d1152, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49148 (p : Pattern) (guard : d8113 p = 1) : d1194 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1194, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49147 p hg
    simpa only [d8113, d1194, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1194, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49125 p hg
    simpa only [d8113, d1194, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49149 (p : Pattern) (guard : d8118 p = 1) : d1179 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1179, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48990 p hg
    simpa only [d8118, d1179, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1179, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d8118, d1179, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49150 (p : Pattern) (guard : d8119 p = 1) : d1195 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1195, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49148 p hg
    simpa only [d8119, d1195, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1195, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49149 p hg
    simpa only [d8119, d1195, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49151 (p : Pattern) (guard : d8112 p = 1) : d1212 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1212, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35497 p hg
    simpa only [d8112, d1212, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1212, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1212, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49152 (p : Pattern) (guard : d8117 p = 1) : d1158 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35501 p hg
    simpa only [d8117, d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49153 (p : Pattern) (guard : d8118 p = 1) : d1213 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1213, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49151 p hg
    simpa only [d8118, d1213, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1213, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49152 p hg
    simpa only [d8118, d1213, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49154 (p : Pattern) (guard : d8117 p = 1) : d1160 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35504 p hg
    simpa only [d8117, d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49155 (p : Pattern) (guard : d8123 p = 1) : d1161 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49154 p hg
    simpa only [d8123, d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4221 p hg
    simpa only [d8123, d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49156 (p : Pattern) (guard : d8124 p = 1) : d1214 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1214, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49153 p hg
    simpa only [d8124, d1214, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1214, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49155 p hg
    simpa only [d8124, d1214, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49157 (p : Pattern) (guard : d8125 p = 1) : d1260 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1260, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49150 p hg
    simpa only [d8125, d1260, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1260, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49156 p hg
    simpa only [d8125, d1260, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49158 (p : Pattern) (guard : d8112 p = 1) : d1197 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1197, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35513 p hg
    simpa only [d8112, d1197, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1197, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48151 p hg
    simpa only [d8112, d1197, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49159 (p : Pattern) (guard : d8118 p = 1) : d1198 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1198, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49158 p hg
    simpa only [d8118, d1198, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1198, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48110 p hg
    simpa only [d8118, d1198, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49160 (p : Pattern) (guard : d8123 p = 1) : d1182 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1182, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48095 p hg
    simpa only [d8123, d1182, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1182, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d8123, d1182, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49161 (p : Pattern) (guard : d8124 p = 1) : d1199 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1199, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49159 p hg
    simpa only [d8124, d1199, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1199, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49160 p hg
    simpa only [d8124, d1199, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49162 (p : Pattern) (guard : d8123 p = 1) : d1218 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47865 p hg
    simpa only [d8123, d1218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d8123, d1218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49163 (p : Pattern) (guard : d0 p = 1) : d1173 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49164 (p : Pattern) (guard : d8129 p = 1) : d1219 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49162 p hg
    simpa only [d8129, d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49163 p hg
    simpa only [d8129, d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49165 (p : Pattern) (guard : d8130 p = 1) : d1261 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1261, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49161 p hg
    simpa only [d8130, d1261, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1261, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49164 p hg
    simpa only [d8130, d1261, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49166 (p : Pattern) (guard : d8131 p = 1) : d1262 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1262, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49157 p hg
    simpa only [d8131, d1262, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1262, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49165 p hg
    simpa only [d8131, d1262, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49167 (p : Pattern) (guard : d8117 p = 1) : d1177 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35539 p hg
    simpa only [d8117, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49168 (p : Pattern) (guard : d8118 p = 1) : d1177 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48990 p hg
    simpa only [d8118, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49167 p hg
    simpa only [d8118, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49169 (p : Pattern) (guard : d8123 p = 1) : d1179 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49167 p hg
    simpa only [d8123, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4229 p hg
    simpa only [d8123, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49170 (p : Pattern) (guard : d8124 p = 1) : d1263 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1263, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49168 p hg
    simpa only [d8124, d1263, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1263, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49169 p hg
    simpa only [d8124, d1263, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49171 (p : Pattern) (guard : d8129 p = 1) : d1183 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48919 p hg
    simpa only [d8129, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49172 (p : Pattern) (guard : d8130 p = 1) : d1264 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1264, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49170 p hg
    simpa only [d8130, d1264, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1264, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49171 p hg
    simpa only [d8130, d1264, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49173 (p : Pattern) (guard : d8123 p = 1) : d1181 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48095 p hg
    simpa only [d8123, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d8123, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49174 (p : Pattern) (guard : d0 p = 1) : d1182 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49175 (p : Pattern) (guard : d8129 p = 1) : d1346 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1346, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49173 p hg
    simpa only [d8129, d1346, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1346, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49174 p hg
    simpa only [d8129, d1346, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49176 (p : Pattern) (guard : d0 p = 1) : d1349 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49177 (p : Pattern) (guard : d8135 p = 1) : d1350 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1350, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49175 p hg
    simpa only [d8135, d1350, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1350, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49176 p hg
    simpa only [d8135, d1350, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49178 (p : Pattern) (guard : d8136 p = 1) : d1351 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1351, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49172 p hg
    simpa only [d8136, d1351, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1351, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49177 p hg
    simpa only [d8136, d1351, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49179 (p : Pattern) (guard : d8137 p = 1) : d1352 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1352, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49166 p hg
    simpa only [d8137, d1352, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1352, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49178 p hg
    simpa only [d8137, d1352, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49180 (p : Pattern) (guard : d8118 p = 1) : d1222 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1222, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49125 p hg
    simpa only [d8118, d1222, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1222, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49167 p hg
    simpa only [d8118, d1222, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49181 (p : Pattern) (guard : d8124 p = 1) : d1223 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1223, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49180 p hg
    simpa only [d8124, d1223, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1223, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49169 p hg
    simpa only [d8124, d1223, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49182 (p : Pattern) (guard : d8130 p = 1) : d1224 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1224, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49181 p hg
    simpa only [d8130, d1224, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1224, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49171 p hg
    simpa only [d8130, d1224, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49183 (p : Pattern) (guard : d8123 p = 1) : d1181 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48110 p hg
    simpa only [d8123, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d8123, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49184 (p : Pattern) (guard : d8129 p = 1) : d1346 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1346, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49183 p hg
    simpa only [d8129, d1346, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1346, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49174 p hg
    simpa only [d8129, d1346, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49185 (p : Pattern) (guard : d8135 p = 1) : d1350 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1350, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49184 p hg
    simpa only [d8135, d1350, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1350, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49176 p hg
    simpa only [d8135, d1350, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49186 (p : Pattern) (guard : d8136 p = 1) : d1353 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1353, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49182 p hg
    simpa only [d8136, d1353, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1353, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49185 p hg
    simpa only [d8136, d1353, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49187 (p : Pattern) (guard : d8142 p = 1) : d1354 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1354, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49186 p hg
    simpa only [d8142, d1354, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1354, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d1354, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49188 (p : Pattern) (guard : d8143 p = 1) : d1355 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1355, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49179 p hg
    simpa only [d8143, d1355, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1355, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49187 p hg
    simpa only [d8143, d1355, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49189 (p : Pattern) (guard : d8144 p = 1) : d1356 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d1356, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49146 p hg
    simpa only [d8144, d1356, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d1356, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49188 p hg
    simpa only [d8144, d1356, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49190 (p : Pattern) (guard : d8145 p = 1) : d1357 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d1357, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48997 p hg
    simpa only [d8145, d1357, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d1357, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49189 p hg
    simpa only [d8145, d1357, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49191 (p : Pattern) (guard : d8101 p = 1) : d337 p ≤ (0 : Int) + d337 p := by
  omega
theorem compare49192 (p : Pattern) (guard : d8102 p = 1) : d1151 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1151, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35566 p hg
    simpa only [d8102, d1151, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1151, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49191 p hg
    simpa only [d8102, d1151, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49193 (p : Pattern) (guard : d8108 p = 1) : d1153 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1153, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49192 p hg
    simpa only [d8108, d1153, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1153, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49147 p hg
    simpa only [d8108, d1153, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49194 (p : Pattern) (guard : d8113 p = 1) : d1155 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1155, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48978 p hg
    simpa only [d8113, d1155, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1155, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35570 p hg
    simpa only [d8113, d1155, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49195 (p : Pattern) (guard : d8114 p = 1) : d1156 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1156, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49193 p hg
    simpa only [d8114, d1156, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1156, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49194 p hg
    simpa only [d8114, d1156, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49196 (p : Pattern) (guard : d8107 p = 1) : d1157 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1157, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35573 p hg
    simpa only [d8107, d1157, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1157, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47893 p hg
    simpa only [d8107, d1157, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49197 (p : Pattern) (guard : d8112 p = 1) : d1158 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1158, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35575 p hg
    simpa only [d8112, d1158, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1158, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1158, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49198 (p : Pattern) (guard : d8113 p = 1) : d1159 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1159, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49196 p hg
    simpa only [d8113, d1159, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1159, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49197 p hg
    simpa only [d8113, d1159, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49199 (p : Pattern) (guard : d8112 p = 1) : d1160 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1160, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35578 p hg
    simpa only [d8112, d1160, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1160, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1160, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49200 (p : Pattern) (guard : d8118 p = 1) : d1161 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1161, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49199 p hg
    simpa only [d8118, d1161, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1161, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34871 p hg
    simpa only [d8118, d1161, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49201 (p : Pattern) (guard : d8119 p = 1) : d1162 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1162, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49198 p hg
    simpa only [d8119, d1162, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1162, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49200 p hg
    simpa only [d8119, d1162, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49202 (p : Pattern) (guard : d8120 p = 1) : d1163 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1163, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49195 p hg
    simpa only [d8120, d1163, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1163, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49201 p hg
    simpa only [d8120, d1163, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49203 (p : Pattern) (guard : d8106 p = 1) : d352 p ≤ (0 : Int) + d352 p := by
  omega
theorem compare49204 (p : Pattern) (guard : d8107 p = 1) : d1164 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1164, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35587 p hg
    simpa only [d8107, d1164, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1164, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49203 p hg
    simpa only [d8107, d1164, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49205 (p : Pattern) (guard : d8113 p = 1) : d1166 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1166, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49204 p hg
    simpa only [d8113, d1166, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1166, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48152 p hg
    simpa only [d8113, d1166, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49206 (p : Pattern) (guard : d8118 p = 1) : d1168 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1168, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48070 p hg
    simpa only [d8118, d1168, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1168, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35606 p hg
    simpa only [d8118, d1168, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49207 (p : Pattern) (guard : d8119 p = 1) : d1169 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1169, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49205 p hg
    simpa only [d8119, d1169, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1169, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49206 p hg
    simpa only [d8119, d1169, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49208 (p : Pattern) (guard : d8118 p = 1) : d1172 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1172, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49114 p hg
    simpa only [d8118, d1172, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1172, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47853 p hg
    simpa only [d8118, d1172, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49209 (p : Pattern) (guard : d8124 p = 1) : d1174 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1174, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49208 p hg
    simpa only [d8124, d1174, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1174, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48907 p hg
    simpa only [d8124, d1174, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49210 (p : Pattern) (guard : d8125 p = 1) : d1175 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1175, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49207 p hg
    simpa only [d8125, d1175, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1175, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49209 p hg
    simpa only [d8125, d1175, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49211 (p : Pattern) (guard : d8126 p = 1) : d1176 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1176, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49202 p hg
    simpa only [d8126, d1176, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1176, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49210 p hg
    simpa only [d8126, d1176, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49212 (p : Pattern) (guard : d8132 p = 1) : d1192 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1192, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49211 p hg
    simpa only [d8132, d1192, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1192, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49140 p hg
    simpa only [d8132, d1192, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49213 (p : Pattern) (guard : d8124 p = 1) : d1183 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1183, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48980 p hg
    simpa only [d8124, d1183, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1183, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1183, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49214 (p : Pattern) (guard : d8125 p = 1) : d1196 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1196, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49150 p hg
    simpa only [d8125, d1196, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1196, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49213 p hg
    simpa only [d8125, d1196, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49215 (p : Pattern) (guard : d8130 p = 1) : d1200 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1200, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49161 p hg
    simpa only [d8130, d1200, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1200, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48922 p hg
    simpa only [d8130, d1200, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49216 (p : Pattern) (guard : d8131 p = 1) : d1201 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1201, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49214 p hg
    simpa only [d8131, d1201, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1201, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49215 p hg
    simpa only [d8131, d1201, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49217 (p : Pattern) (guard : d8118 p = 1) : d1202 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1202, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35570 p hg
    simpa only [d8118, d1202, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1202, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d1202, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49218 (p : Pattern) (guard : d8124 p = 1) : d1203 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1203, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49217 p hg
    simpa only [d8124, d1203, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1203, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38245 p hg
    simpa only [d8124, d1203, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49219 (p : Pattern) (guard : d8130 p = 1) : d1204 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1204, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49218 p hg
    simpa only [d8130, d1204, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1204, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38247 p hg
    simpa only [d8130, d1204, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49220 (p : Pattern) (guard : d8136 p = 1) : d1205 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1205, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49219 p hg
    simpa only [d8136, d1205, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1205, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41492 p hg
    simpa only [d8136, d1205, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49221 (p : Pattern) (guard : d8137 p = 1) : d1206 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1206, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49216 p hg
    simpa only [d8137, d1206, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1206, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49220 p hg
    simpa only [d8137, d1206, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49222 (p : Pattern) (guard : d8138 p = 1) : d1207 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1207, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49212 p hg
    simpa only [d8138, d1207, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1207, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49221 p hg
    simpa only [d8138, d1207, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49223 (p : Pattern) (guard : d8113 p = 1) : d1209 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1209, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49112 p hg
    simpa only [d8113, d1209, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1209, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49136 p hg
    simpa only [d8113, d1209, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49224 (p : Pattern) (guard : d8118 p = 1) : d1210 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1210, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49125 p hg
    simpa only [d8118, d1210, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1210, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d8118, d1210, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49225 (p : Pattern) (guard : d8119 p = 1) : d1211 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1211, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49223 p hg
    simpa only [d8119, d1211, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1211, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49224 p hg
    simpa only [d8119, d1211, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49226 (p : Pattern) (guard : d8112 p = 1) : d1212 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1212, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35644 p hg
    simpa only [d8112, d1212, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1212, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1212, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49227 (p : Pattern) (guard : d8118 p = 1) : d1213 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1213, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49226 p hg
    simpa only [d8118, d1213, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1213, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49152 p hg
    simpa only [d8118, d1213, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49228 (p : Pattern) (guard : d8124 p = 1) : d1214 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1214, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49227 p hg
    simpa only [d8124, d1214, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1214, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49155 p hg
    simpa only [d8124, d1214, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49229 (p : Pattern) (guard : d8125 p = 1) : d1215 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1215, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49225 p hg
    simpa only [d8125, d1215, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1215, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49228 p hg
    simpa only [d8125, d1215, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49230 (p : Pattern) (guard : d8112 p = 1) : d1154 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1154, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35653 p hg
    simpa only [d8112, d1154, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1154, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35854 p hg
    simpa only [d8112, d1154, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49231 (p : Pattern) (guard : d8118 p = 1) : d1216 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1216, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49230 p hg
    simpa only [d8118, d1216, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1216, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48184 p hg
    simpa only [d8118, d1216, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49232 (p : Pattern) (guard : d8123 p = 1) : d1182 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1182, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48110 p hg
    simpa only [d8123, d1182, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1182, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d8123, d1182, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49233 (p : Pattern) (guard : d8124 p = 1) : d1217 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1217, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49231 p hg
    simpa only [d8124, d1217, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1217, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49232 p hg
    simpa only [d8124, d1217, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49234 (p : Pattern) (guard : d8123 p = 1) : d1218 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1218, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48095 p hg
    simpa only [d8123, d1218, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1218, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d8123, d1218, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49235 (p : Pattern) (guard : d8129 p = 1) : d1219 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1219, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49234 p hg
    simpa only [d8129, d1219, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1219, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49163 p hg
    simpa only [d8129, d1219, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49236 (p : Pattern) (guard : d8130 p = 1) : d1220 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1220, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49233 p hg
    simpa only [d8130, d1220, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1220, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49235 p hg
    simpa only [d8130, d1220, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49237 (p : Pattern) (guard : d8131 p = 1) : d1221 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1221, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49229 p hg
    simpa only [d8131, d1221, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1221, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49236 p hg
    simpa only [d8131, d1221, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49238 (p : Pattern) (guard : d8117 p = 1) : d1177 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1177, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35686 p hg
    simpa only [d8117, d1177, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1177, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1177, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49239 (p : Pattern) (guard : d8123 p = 1) : d1225 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1225, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49238 p hg
    simpa only [d8123, d1225, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1225, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d8123, d1225, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49240 (p : Pattern) (guard : d8129 p = 1) : d1226 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1226, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49239 p hg
    simpa only [d8129, d1226, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1226, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49174 p hg
    simpa only [d8129, d1226, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49241 (p : Pattern) (guard : d0 p = 1) : d1189 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49242 (p : Pattern) (guard : d8135 p = 1) : d1227 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1227, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49240 p hg
    simpa only [d8135, d1227, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1227, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49241 p hg
    simpa only [d8135, d1227, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49243 (p : Pattern) (guard : d8136 p = 1) : d1228 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1228, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49182 p hg
    simpa only [d8136, d1228, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1228, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49242 p hg
    simpa only [d8136, d1228, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49244 (p : Pattern) (guard : d8137 p = 1) : d1229 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1229, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49237 p hg
    simpa only [d8137, d1229, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1229, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49243 p hg
    simpa only [d8137, d1229, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49245 (p : Pattern) (guard : d8117 p = 1) : d1177 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1177, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35553 p hg
    simpa only [d8117, d1177, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1177, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1177, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49246 (p : Pattern) (guard : d8118 p = 1) : d1230 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1230, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49136 p hg
    simpa only [d8118, d1230, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1230, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49245 p hg
    simpa only [d8118, d1230, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49247 (p : Pattern) (guard : d8124 p = 1) : d1231 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1231, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49246 p hg
    simpa only [d8124, d1231, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1231, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49169 p hg
    simpa only [d8124, d1231, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49248 (p : Pattern) (guard : d8130 p = 1) : d1232 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1232, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49247 p hg
    simpa only [d8130, d1232, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1232, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49171 p hg
    simpa only [d8130, d1232, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49249 (p : Pattern) (guard : d8117 p = 1) : d1177 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1177, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41497 p hg
    simpa only [d8117, d1177, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1177, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1177, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49250 (p : Pattern) (guard : d8123 p = 1) : d1225 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1225, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49249 p hg
    simpa only [d8123, d1225, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1225, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d8123, d1225, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49251 (p : Pattern) (guard : d8129 p = 1) : d1226 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1226, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49250 p hg
    simpa only [d8129, d1226, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1226, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49174 p hg
    simpa only [d8129, d1226, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49252 (p : Pattern) (guard : d8135 p = 1) : d1227 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1227, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49251 p hg
    simpa only [d8135, d1227, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1227, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49241 p hg
    simpa only [d8135, d1227, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49253 (p : Pattern) (guard : d8136 p = 1) : d1233 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1233, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49248 p hg
    simpa only [d8136, d1233, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1233, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49252 p hg
    simpa only [d8136, d1233, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49254 (p : Pattern) (guard : d8142 p = 1) : d1234 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1234, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49253 p hg
    simpa only [d8142, d1234, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1234, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d1234, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49255 (p : Pattern) (guard : d8143 p = 1) : d1235 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1235, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49244 p hg
    simpa only [d8143, d1235, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1235, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49254 p hg
    simpa only [d8143, d1235, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49256 (p : Pattern) (guard : d8144 p = 1) : d1236 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d1236, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49222 p hg
    simpa only [d8144, d1236, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d1236, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49255 p hg
    simpa only [d8144, d1236, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49257 (p : Pattern) (guard : d8106 p = 1) : d344 p ≤ (0 : Int) + d344 p := by
  omega
theorem compare49258 (p : Pattern) (guard : d8107 p = 1) : d1271 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1271, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35700 p hg
    simpa only [d8107, d1271, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1271, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49257 p hg
    simpa only [d8107, d1271, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49259 (p : Pattern) (guard : d8112 p = 1) : d1272 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1272, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35712 p hg
    simpa only [d8112, d1272, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1272, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35854 p hg
    simpa only [d8112, d1272, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49260 (p : Pattern) (guard : d8113 p = 1) : d1273 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1273, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49258 p hg
    simpa only [d8113, d1273, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1273, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49259 p hg
    simpa only [d8113, d1273, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49261 (p : Pattern) (guard : d8118 p = 1) : d1275 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1275, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49068 p hg
    simpa only [d8118, d1275, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1275, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35728 p hg
    simpa only [d8118, d1275, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49262 (p : Pattern) (guard : d8119 p = 1) : d1276 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1276, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49260 p hg
    simpa only [d8119, d1276, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1276, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d8119, d1276, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49263 (p : Pattern) (guard : d8112 p = 1) : d1277 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1277, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35731 p hg
    simpa only [d8112, d1277, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1277, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47959 p hg
    simpa only [d8112, d1277, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49264 (p : Pattern) (guard : d8117 p = 1) : d1278 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1278, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35739 p hg
    simpa only [d8117, d1278, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1278, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1278, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49265 (p : Pattern) (guard : d8118 p = 1) : d1279 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1279, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49263 p hg
    simpa only [d8118, d1279, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1279, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49264 p hg
    simpa only [d8118, d1279, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49266 (p : Pattern) (guard : d8124 p = 1) : d1281 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1281, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49265 p hg
    simpa only [d8124, d1281, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1281, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49065 p hg
    simpa only [d8124, d1281, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49267 (p : Pattern) (guard : d8125 p = 1) : d1282 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1282, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49262 p hg
    simpa only [d8125, d1282, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1282, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49266 p hg
    simpa only [d8125, d1282, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49268 (p : Pattern) (guard : d8112 p = 1) : d1283 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1283, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35750 p hg
    simpa only [d8112, d1283, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1283, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38310 p hg
    simpa only [d8112, d1283, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49269 (p : Pattern) (guard : d8118 p = 1) : d1358 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1358, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49268 p hg
    simpa only [d8118, d1358, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1358, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48223 p hg
    simpa only [d8118, d1358, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49270 (p : Pattern) (guard : d8117 p = 1) : d1289 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1289, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48230 p hg
    simpa only [d8117, d1289, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1289, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35767 p hg
    simpa only [d8117, d1289, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49271 (p : Pattern) (guard : d8123 p = 1) : d1300 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1300, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49270 p hg
    simpa only [d8123, d1300, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1300, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1300, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49272 (p : Pattern) (guard : d8124 p = 1) : d1359 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1359, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49269 p hg
    simpa only [d8124, d1359, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1359, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49271 p hg
    simpa only [d8124, d1359, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49273 (p : Pattern) (guard : d8117 p = 1) : d1289 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1289, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35335 p hg
    simpa only [d8117, d1289, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1289, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1289, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49274 (p : Pattern) (guard : d8123 p = 1) : d1291 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1291, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49273 p hg
    simpa only [d8123, d1291, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1291, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10219 p hg
    simpa only [d8123, d1291, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49275 (p : Pattern) (guard : d8129 p = 1) : d1293 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1293, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49274 p hg
    simpa only [d8129, d1293, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1293, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49073 p hg
    simpa only [d8129, d1293, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49276 (p : Pattern) (guard : d8130 p = 1) : d1360 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1360, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49272 p hg
    simpa only [d8130, d1360, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1360, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49275 p hg
    simpa only [d8130, d1360, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49277 (p : Pattern) (guard : d8131 p = 1) : d1361 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1361, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49267 p hg
    simpa only [d8131, d1361, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1361, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49276 p hg
    simpa only [d8131, d1361, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49278 (p : Pattern) (guard : d8118 p = 1) : d1297 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1297, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49068 p hg
    simpa only [d8118, d1297, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1297, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49093 p hg
    simpa only [d8118, d1297, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49279 (p : Pattern) (guard : d8123 p = 1) : d1298 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1298, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49082 p hg
    simpa only [d8123, d1298, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1298, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d8123, d1298, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
