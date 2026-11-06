/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons347
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare48720 (p : Pattern) (guard : d8149 p = 1) : d945 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d945, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48701 p hg
    simpa only [d8149, d945, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d945, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48719 p hg
    simpa only [d8149, d945, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48721 (p : Pattern) (guard : d8150 p = 1) : d946 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d946, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48676 p hg
    simpa only [d8150, d946, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d946, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48720 p hg
    simpa only [d8150, d946, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48722 (p : Pattern) (guard : d8151 p = 1) : d947 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48628 p hg
    simpa only [d8151, d947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48721 p hg
    simpa only [d8151, d947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48723 (p : Pattern) (guard : d8152 p = 1) : d948 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48575 p hg
    simpa only [d8152, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48722 p hg
    simpa only [d8152, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48724 (p : Pattern) (guard : d8092 p = 1) : d337 p ≤ (0 : Int) + d337 p := by
  omega
theorem compare48725 (p : Pattern) (guard : d8093 p = 1) : d1151 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8088 p = 1 := by simpa only [d8093, d1151, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34330 p hg
    simpa only [d8093, d1151, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8092 p = 1 := by simpa only [d8093, d1151, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48724 p hg
    simpa only [d8093, d1151, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48726 (p : Pattern) (guard : d8096 p = 1) : d345 p ≤ (0 : Int) + d345 p := by
  omega
theorem compare48727 (p : Pattern) (guard : d8097 p = 1) : d1152 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1152, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34354 p hg
    simpa only [d8097, d1152, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1152, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48726 p hg
    simpa only [d8097, d1152, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48728 (p : Pattern) (guard : d8098 p = 1) : d1153 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8093 p = 1 := by simpa only [d8098, d1153, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48725 p hg
    simpa only [d8098, d1153, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8097 p = 1 := by simpa only [d8098, d1153, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48727 p hg
    simpa only [d8098, d1153, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48729 (p : Pattern) (guard : d8096 p = 1) : d354 p ≤ (0 : Int) + d354 p := by
  omega
theorem compare48730 (p : Pattern) (guard : d8097 p = 1) : d1154 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1154, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34377 p hg
    simpa only [d8097, d1154, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1154, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48729 p hg
    simpa only [d8097, d1154, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48731 (p : Pattern) (guard : d8103 p = 1) : d1155 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1155, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48730 p hg
    simpa only [d8103, d1155, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1155, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34400 p hg
    simpa only [d8103, d1155, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48732 (p : Pattern) (guard : d8104 p = 1) : d1156 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8098 p = 1 := by simpa only [d8104, d1156, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48728 p hg
    simpa only [d8104, d1156, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8103 p = 1 := by simpa only [d8104, d1156, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48731 p hg
    simpa only [d8104, d1156, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48733 (p : Pattern) (guard : d8096 p = 1) : d360 p ≤ (0 : Int) + d360 p := by
  omega
theorem compare48734 (p : Pattern) (guard : d8097 p = 1) : d1157 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1157, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34412 p hg
    simpa only [d8097, d1157, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1157, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48733 p hg
    simpa only [d8097, d1157, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48735 (p : Pattern) (guard : d8102 p = 1) : d1158 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1158, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34439 p hg
    simpa only [d8102, d1158, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1158, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d8102, d1158, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48736 (p : Pattern) (guard : d8103 p = 1) : d1159 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1159, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48734 p hg
    simpa only [d8103, d1159, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1159, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48735 p hg
    simpa only [d8103, d1159, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48737 (p : Pattern) (guard : d8102 p = 1) : d1160 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1160, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34449 p hg
    simpa only [d8102, d1160, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1160, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d8102, d1160, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48738 (p : Pattern) (guard : d8108 p = 1) : d1161 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1161, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48737 p hg
    simpa only [d8108, d1161, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1161, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34456 p hg
    simpa only [d8108, d1161, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48739 (p : Pattern) (guard : d8109 p = 1) : d1162 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1162, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48736 p hg
    simpa only [d8109, d1162, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1162, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48738 p hg
    simpa only [d8109, d1162, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48740 (p : Pattern) (guard : d8110 p = 1) : d1163 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8104 p = 1 := by simpa only [d8110, d1163, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48732 p hg
    simpa only [d8110, d1163, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8109 p = 1 := by simpa only [d8110, d1163, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48739 p hg
    simpa only [d8110, d1163, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48741 (p : Pattern) (guard : d8096 p = 1) : d352 p ≤ (0 : Int) + d352 p := by
  omega
theorem compare48742 (p : Pattern) (guard : d8097 p = 1) : d1164 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1164, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34466 p hg
    simpa only [d8097, d1164, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1164, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48741 p hg
    simpa only [d8097, d1164, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48743 (p : Pattern) (guard : d8103 p = 1) : d1166 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1166, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48742 p hg
    simpa only [d8103, d1166, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1166, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47690 p hg
    simpa only [d8103, d1166, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48744 (p : Pattern) (guard : d8101 p = 1) : d370 p ≤ (0 : Int) + d370 p := by
  omega
theorem compare48745 (p : Pattern) (guard : d8102 p = 1) : d1167 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1167, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47697 p hg
    simpa only [d8102, d1167, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1167, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48744 p hg
    simpa only [d8102, d1167, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48746 (p : Pattern) (guard : d8108 p = 1) : d1168 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1168, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48745 p hg
    simpa only [d8108, d1168, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1168, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34515 p hg
    simpa only [d8108, d1168, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48747 (p : Pattern) (guard : d8109 p = 1) : d1169 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1169, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48743 p hg
    simpa only [d8109, d1169, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1169, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48746 p hg
    simpa only [d8109, d1169, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48748 (p : Pattern) (guard : d8101 p = 1) : d373 p ≤ (0 : Int) + d373 p := by
  omega
theorem compare48749 (p : Pattern) (guard : d8102 p = 1) : d1170 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1170, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47705 p hg
    simpa only [d8102, d1170, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1170, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48748 p hg
    simpa only [d8102, d1170, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48750 (p : Pattern) (guard : d8108 p = 1) : d1172 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1172, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48749 p hg
    simpa only [d8108, d1172, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1172, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47708 p hg
    simpa only [d8108, d1172, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48751 (p : Pattern) (guard : d8113 p = 1) : d1173 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47708 p hg
    simpa only [d8113, d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34544 p hg
    simpa only [d8113, d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48752 (p : Pattern) (guard : d8114 p = 1) : d1174 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1174, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48750 p hg
    simpa only [d8114, d1174, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1174, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48751 p hg
    simpa only [d8114, d1174, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48753 (p : Pattern) (guard : d8115 p = 1) : d1175 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1175, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48747 p hg
    simpa only [d8115, d1175, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1175, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48752 p hg
    simpa only [d8115, d1175, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48754 (p : Pattern) (guard : d8116 p = 1) : d1176 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8110 p = 1 := by simpa only [d8116, d1176, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48740 p hg
    simpa only [d8116, d1176, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8115 p = 1 := by simpa only [d8116, d1176, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48753 p hg
    simpa only [d8116, d1176, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48755 (p : Pattern) (guard : d8102 p = 1) : d1177 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1177, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34552 p hg
    simpa only [d8102, d1177, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1177, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d8102, d1177, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48756 (p : Pattern) (guard : d8103 p = 1) : d1178 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1178, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48730 p hg
    simpa only [d8103, d1178, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1178, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48755 p hg
    simpa only [d8103, d1178, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48757 (p : Pattern) (guard : d8102 p = 1) : d1177 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1177, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34557 p hg
    simpa only [d8102, d1177, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1177, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d8102, d1177, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48758 (p : Pattern) (guard : d8108 p = 1) : d1179 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1179, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48757 p hg
    simpa only [d8108, d1179, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1179, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34560 p hg
    simpa only [d8108, d1179, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48759 (p : Pattern) (guard : d8109 p = 1) : d1180 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1180, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48756 p hg
    simpa only [d8109, d1180, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1180, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48758 p hg
    simpa only [d8109, d1180, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48760 (p : Pattern) (guard : d8102 p = 1) : d1181 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1181, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34566 p hg
    simpa only [d8102, d1181, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1181, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d8102, d1181, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48761 (p : Pattern) (guard : d8108 p = 1) : d1182 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1182, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48760 p hg
    simpa only [d8108, d1182, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1182, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34575 p hg
    simpa only [d8108, d1182, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48762 (p : Pattern) (guard : d8114 p = 1) : d1183 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1183, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48761 p hg
    simpa only [d8114, d1183, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1183, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d1183, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48763 (p : Pattern) (guard : d8115 p = 1) : d1184 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1184, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48759 p hg
    simpa only [d8115, d1184, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1184, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48762 p hg
    simpa only [d8115, d1184, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48764 (p : Pattern) (guard : d8102 p = 1) : d1185 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1185, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34582 p hg
    simpa only [d8102, d1185, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1185, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48744 p hg
    simpa only [d8102, d1185, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48765 (p : Pattern) (guard : d8108 p = 1) : d1186 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1186, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48764 p hg
    simpa only [d8108, d1186, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1186, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47720 p hg
    simpa only [d8108, d1186, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48766 (p : Pattern) (guard : d8107 p = 1) : d1181 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34708 p hg
    simpa only [d8107, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48767 (p : Pattern) (guard : d8113 p = 1) : d1182 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48766 p hg
    simpa only [d8113, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48768 (p : Pattern) (guard : d8114 p = 1) : d1187 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1187, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48765 p hg
    simpa only [d8114, d1187, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1187, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48767 p hg
    simpa only [d8114, d1187, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48769 (p : Pattern) (guard : d8113 p = 1) : d1188 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48766 p hg
    simpa only [d8113, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48770 (p : Pattern) (guard : d8119 p = 1) : d1189 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48769 p hg
    simpa only [d8119, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48771 (p : Pattern) (guard : d8120 p = 1) : d1190 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1190, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48768 p hg
    simpa only [d8120, d1190, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1190, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48770 p hg
    simpa only [d8120, d1190, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48772 (p : Pattern) (guard : d8121 p = 1) : d1191 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1191, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48763 p hg
    simpa only [d8121, d1191, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1191, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48771 p hg
    simpa only [d8121, d1191, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48773 (p : Pattern) (guard : d8122 p = 1) : d1192 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8116 p = 1 := by simpa only [d8122, d1192, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48754 p hg
    simpa only [d8122, d1192, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8121 p = 1 := by simpa only [d8122, d1192, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48772 p hg
    simpa only [d8122, d1192, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48774 (p : Pattern) (guard : d8102 p = 1) : d1193 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1193, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34550 p hg
    simpa only [d8102, d1193, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1193, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48748 p hg
    simpa only [d8102, d1193, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48775 (p : Pattern) (guard : d8103 p = 1) : d1194 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1194, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48727 p hg
    simpa only [d8103, d1194, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1194, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48774 p hg
    simpa only [d8103, d1194, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48776 (p : Pattern) (guard : d8108 p = 1) : d1179 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1179, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48755 p hg
    simpa only [d8108, d1179, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1179, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34560 p hg
    simpa only [d8108, d1179, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48777 (p : Pattern) (guard : d8109 p = 1) : d1195 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1195, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48775 p hg
    simpa only [d8109, d1195, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1195, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48776 p hg
    simpa only [d8109, d1195, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48778 (p : Pattern) (guard : d8102 p = 1) : d1181 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1181, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38110 p hg
    simpa only [d8102, d1181, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1181, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d8102, d1181, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48779 (p : Pattern) (guard : d8108 p = 1) : d1182 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1182, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48778 p hg
    simpa only [d8108, d1182, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1182, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34575 p hg
    simpa only [d8108, d1182, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48780 (p : Pattern) (guard : d8114 p = 1) : d1183 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1183, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48779 p hg
    simpa only [d8114, d1183, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1183, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d1183, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48781 (p : Pattern) (guard : d8115 p = 1) : d1196 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1196, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48777 p hg
    simpa only [d8115, d1196, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1196, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48780 p hg
    simpa only [d8115, d1196, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48782 (p : Pattern) (guard : d8102 p = 1) : d1197 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1197, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34622 p hg
    simpa only [d8102, d1197, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1197, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47689 p hg
    simpa only [d8102, d1197, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48783 (p : Pattern) (guard : d8108 p = 1) : d1198 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1198, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48782 p hg
    simpa only [d8108, d1198, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1198, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47737 p hg
    simpa only [d8108, d1198, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48784 (p : Pattern) (guard : d8113 p = 1) : d1182 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1182, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47720 p hg
    simpa only [d8113, d1182, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1182, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d1182, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48785 (p : Pattern) (guard : d8114 p = 1) : d1199 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1199, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48783 p hg
    simpa only [d8114, d1199, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1199, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48784 p hg
    simpa only [d8114, d1199, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48786 (p : Pattern) (guard : d8120 p = 1) : d1200 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1200, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48785 p hg
    simpa only [d8120, d1200, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1200, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48770 p hg
    simpa only [d8120, d1200, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48787 (p : Pattern) (guard : d8121 p = 1) : d1201 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1201, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48781 p hg
    simpa only [d8121, d1201, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1201, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48786 p hg
    simpa only [d8121, d1201, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48788 (p : Pattern) (guard : d8108 p = 1) : d1202 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1202, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34400 p hg
    simpa only [d8108, d1202, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1202, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34575 p hg
    simpa only [d8108, d1202, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48789 (p : Pattern) (guard : d8114 p = 1) : d1203 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1203, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48788 p hg
    simpa only [d8114, d1203, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1203, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38119 p hg
    simpa only [d8114, d1203, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48790 (p : Pattern) (guard : d8120 p = 1) : d1204 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1204, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48789 p hg
    simpa only [d8120, d1204, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1204, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38121 p hg
    simpa only [d8120, d1204, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48791 (p : Pattern) (guard : d8126 p = 1) : d1205 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1205, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48790 p hg
    simpa only [d8126, d1205, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1205, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41388 p hg
    simpa only [d8126, d1205, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48792 (p : Pattern) (guard : d8127 p = 1) : d1206 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1206, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48787 p hg
    simpa only [d8127, d1206, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1206, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48791 p hg
    simpa only [d8127, d1206, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48793 (p : Pattern) (guard : d8128 p = 1) : d1207 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d1207, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48773 p hg
    simpa only [d8128, d1207, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d1207, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48792 p hg
    simpa only [d8128, d1207, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48794 (p : Pattern) (guard : d8096 p = 1) : d368 p ≤ (0 : Int) + d368 p := by
  omega
theorem compare48795 (p : Pattern) (guard : d8097 p = 1) : d1208 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1208, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34346 p hg
    simpa only [d8097, d1208, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1208, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48794 p hg
    simpa only [d8097, d1208, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48796 (p : Pattern) (guard : d8103 p = 1) : d1209 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1209, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48795 p hg
    simpa only [d8103, d1209, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1209, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48764 p hg
    simpa only [d8103, d1209, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48797 (p : Pattern) (guard : d8108 p = 1) : d1210 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1210, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48774 p hg
    simpa only [d8108, d1210, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1210, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34560 p hg
    simpa only [d8108, d1210, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48798 (p : Pattern) (guard : d8109 p = 1) : d1211 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1211, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48796 p hg
    simpa only [d8109, d1211, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1211, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48797 p hg
    simpa only [d8109, d1211, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48799 (p : Pattern) (guard : d8102 p = 1) : d1212 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1212, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34635 p hg
    simpa only [d8102, d1212, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1212, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d8102, d1212, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48800 (p : Pattern) (guard : d8107 p = 1) : d1158 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34641 p hg
    simpa only [d8107, d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48801 (p : Pattern) (guard : d8108 p = 1) : d1213 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1213, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48799 p hg
    simpa only [d8108, d1213, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1213, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48800 p hg
    simpa only [d8108, d1213, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48802 (p : Pattern) (guard : d8107 p = 1) : d1160 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34647 p hg
    simpa only [d8107, d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48803 (p : Pattern) (guard : d8113 p = 1) : d1161 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48802 p hg
    simpa only [d8113, d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34649 p hg
    simpa only [d8113, d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48804 (p : Pattern) (guard : d8114 p = 1) : d1214 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1214, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48801 p hg
    simpa only [d8114, d1214, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1214, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48803 p hg
    simpa only [d8114, d1214, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48805 (p : Pattern) (guard : d8115 p = 1) : d1215 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1215, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48798 p hg
    simpa only [d8115, d1215, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1215, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48804 p hg
    simpa only [d8115, d1215, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48806 (p : Pattern) (guard : d8101 p = 1) : d354 p ≤ (0 : Int) + d354 p := by
  omega
theorem compare48807 (p : Pattern) (guard : d8102 p = 1) : d1154 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1154, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34655 p hg
    simpa only [d8102, d1154, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1154, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48806 p hg
    simpa only [d8102, d1154, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48808 (p : Pattern) (guard : d8108 p = 1) : d1216 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1216, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48807 p hg
    simpa only [d8108, d1216, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1216, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47755 p hg
    simpa only [d8108, d1216, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48809 (p : Pattern) (guard : d8113 p = 1) : d1182 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1182, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47737 p hg
    simpa only [d8113, d1182, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1182, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d1182, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48810 (p : Pattern) (guard : d8114 p = 1) : d1217 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1217, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48808 p hg
    simpa only [d8114, d1217, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1217, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48809 p hg
    simpa only [d8114, d1217, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48811 (p : Pattern) (guard : d8113 p = 1) : d1218 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1218, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47720 p hg
    simpa only [d8113, d1218, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1218, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47762 p hg
    simpa only [d8113, d1218, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48812 (p : Pattern) (guard : d8118 p = 1) : d1173 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47762 p hg
    simpa only [d8118, d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34691 p hg
    simpa only [d8118, d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48813 (p : Pattern) (guard : d8119 p = 1) : d1219 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1219, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48811 p hg
    simpa only [d8119, d1219, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1219, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48812 p hg
    simpa only [d8119, d1219, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48814 (p : Pattern) (guard : d8120 p = 1) : d1220 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1220, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48810 p hg
    simpa only [d8120, d1220, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1220, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48813 p hg
    simpa only [d8120, d1220, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48815 (p : Pattern) (guard : d8121 p = 1) : d1221 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1221, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48805 p hg
    simpa only [d8121, d1221, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1221, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48814 p hg
    simpa only [d8121, d1221, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48816 (p : Pattern) (guard : d8107 p = 1) : d1177 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34699 p hg
    simpa only [d8107, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48817 (p : Pattern) (guard : d8108 p = 1) : d1222 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1222, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48774 p hg
    simpa only [d8108, d1222, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1222, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48816 p hg
    simpa only [d8108, d1222, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48818 (p : Pattern) (guard : d8113 p = 1) : d1179 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48816 p hg
    simpa only [d8113, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d8113, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48819 (p : Pattern) (guard : d8114 p = 1) : d1223 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1223, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48817 p hg
    simpa only [d8114, d1223, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1223, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48818 p hg
    simpa only [d8114, d1223, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48820 (p : Pattern) (guard : d8119 p = 1) : d1183 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48767 p hg
    simpa only [d8119, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48821 (p : Pattern) (guard : d8120 p = 1) : d1224 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1224, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48819 p hg
    simpa only [d8120, d1224, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1224, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48820 p hg
    simpa only [d8120, d1224, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48822 (p : Pattern) (guard : d8107 p = 1) : d1177 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1177, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34720 p hg
    simpa only [d8107, d1177, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1177, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1177, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48823 (p : Pattern) (guard : d8113 p = 1) : d1225 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1225, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48822 p hg
    simpa only [d8113, d1225, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1225, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47774 p hg
    simpa only [d8113, d1225, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48824 (p : Pattern) (guard : d8118 p = 1) : d1182 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47774 p hg
    simpa only [d8118, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48825 (p : Pattern) (guard : d8119 p = 1) : d1226 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1226, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48823 p hg
    simpa only [d8119, d1226, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1226, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48824 p hg
    simpa only [d8119, d1226, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48826 (p : Pattern) (guard : d8118 p = 1) : d1188 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47774 p hg
    simpa only [d8118, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48827 (p : Pattern) (guard : d8124 p = 1) : d1189 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48826 p hg
    simpa only [d8124, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48828 (p : Pattern) (guard : d8125 p = 1) : d1227 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1227, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48825 p hg
    simpa only [d8125, d1227, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1227, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48827 p hg
    simpa only [d8125, d1227, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48829 (p : Pattern) (guard : d8126 p = 1) : d1228 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1228, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48821 p hg
    simpa only [d8126, d1228, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1228, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48828 p hg
    simpa only [d8126, d1228, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48830 (p : Pattern) (guard : d8127 p = 1) : d1229 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1229, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48815 p hg
    simpa only [d8127, d1229, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1229, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48829 p hg
    simpa only [d8127, d1229, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48831 (p : Pattern) (guard : d8107 p = 1) : d1177 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1177, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34697 p hg
    simpa only [d8107, d1177, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1177, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1177, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48832 (p : Pattern) (guard : d8108 p = 1) : d1230 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1230, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48764 p hg
    simpa only [d8108, d1230, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1230, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48831 p hg
    simpa only [d8108, d1230, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48833 (p : Pattern) (guard : d8114 p = 1) : d1231 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1231, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48832 p hg
    simpa only [d8114, d1231, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1231, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48818 p hg
    simpa only [d8114, d1231, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48834 (p : Pattern) (guard : d8120 p = 1) : d1232 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1232, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48833 p hg
    simpa only [d8120, d1232, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1232, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48820 p hg
    simpa only [d8120, d1232, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48835 (p : Pattern) (guard : d8107 p = 1) : d1177 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1177, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34819 p hg
    simpa only [d8107, d1177, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1177, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1177, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48836 (p : Pattern) (guard : d8113 p = 1) : d1225 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1225, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48835 p hg
    simpa only [d8113, d1225, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1225, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47774 p hg
    simpa only [d8113, d1225, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48837 (p : Pattern) (guard : d8119 p = 1) : d1226 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1226, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48836 p hg
    simpa only [d8119, d1226, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1226, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48824 p hg
    simpa only [d8119, d1226, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48838 (p : Pattern) (guard : d8125 p = 1) : d1227 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1227, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48837 p hg
    simpa only [d8125, d1227, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1227, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48827 p hg
    simpa only [d8125, d1227, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48839 (p : Pattern) (guard : d8126 p = 1) : d1233 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1233, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48834 p hg
    simpa only [d8126, d1233, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1233, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48838 p hg
    simpa only [d8126, d1233, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48840 (p : Pattern) (guard : d8132 p = 1) : d1234 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1234, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48839 p hg
    simpa only [d8132, d1234, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1234, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d8132, d1234, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48841 (p : Pattern) (guard : d8133 p = 1) : d1235 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d1235, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48830 p hg
    simpa only [d8133, d1235, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d1235, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48840 p hg
    simpa only [d8133, d1235, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48842 (p : Pattern) (guard : d8134 p = 1) : d1236 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d1236, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48793 p hg
    simpa only [d8134, d1236, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d1236, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48841 p hg
    simpa only [d8134, d1236, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48843 (p : Pattern) (guard : d8096 p = 1) : d344 p ≤ (0 : Int) + d344 p := by
  omega
theorem compare48844 (p : Pattern) (guard : d8097 p = 1) : d1237 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1237, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34749 p hg
    simpa only [d8097, d1237, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1237, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48843 p hg
    simpa only [d8097, d1237, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48845 (p : Pattern) (guard : d8103 p = 1) : d1238 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1238, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48844 p hg
    simpa only [d8103, d1238, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1238, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48807 p hg
    simpa only [d8103, d1238, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48846 (p : Pattern) (guard : d8108 p = 1) : d1239 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1239, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48782 p hg
    simpa only [d8108, d1239, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1239, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34768 p hg
    simpa only [d8108, d1239, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48847 (p : Pattern) (guard : d8109 p = 1) : d1240 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1240, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48845 p hg
    simpa only [d8109, d1240, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1240, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48846 p hg
    simpa only [d8109, d1240, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48848 (p : Pattern) (guard : d8102 p = 1) : d1241 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1241, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34771 p hg
    simpa only [d8102, d1241, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1241, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48744 p hg
    simpa only [d8102, d1241, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48849 (p : Pattern) (guard : d8107 p = 1) : d1158 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1158, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34774 p hg
    simpa only [d8107, d1158, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1158, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1158, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48850 (p : Pattern) (guard : d8108 p = 1) : d1242 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1242, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48848 p hg
    simpa only [d8108, d1242, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1242, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48849 p hg
    simpa only [d8108, d1242, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48851 (p : Pattern) (guard : d8114 p = 1) : d1243 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1243, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48850 p hg
    simpa only [d8114, d1243, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1243, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48803 p hg
    simpa only [d8114, d1243, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48852 (p : Pattern) (guard : d8115 p = 1) : d1244 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1244, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48847 p hg
    simpa only [d8115, d1244, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1244, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48851 p hg
    simpa only [d8115, d1244, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48853 (p : Pattern) (guard : d8101 p = 1) : d368 p ≤ (0 : Int) + d368 p := by
  omega
theorem compare48854 (p : Pattern) (guard : d8102 p = 1) : d1208 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1208, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34782 p hg
    simpa only [d8102, d1208, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1208, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48853 p hg
    simpa only [d8102, d1208, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48855 (p : Pattern) (guard : d8108 p = 1) : d1245 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1245, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48854 p hg
    simpa only [d8108, d1245, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1245, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47805 p hg
    simpa only [d8108, d1245, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48856 (p : Pattern) (guard : d8106 p = 1) : d373 p ≤ (0 : Int) + d373 p := by
  omega
theorem compare48857 (p : Pattern) (guard : d8107 p = 1) : d1170 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1170, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34661 p hg
    simpa only [d8107, d1170, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1170, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48856 p hg
    simpa only [d8107, d1170, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48858 (p : Pattern) (guard : d8113 p = 1) : d1246 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1246, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48857 p hg
    simpa only [d8113, d1246, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1246, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d1246, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48859 (p : Pattern) (guard : d8114 p = 1) : d1247 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1247, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48855 p hg
    simpa only [d8114, d1247, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1247, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48858 p hg
    simpa only [d8114, d1247, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
