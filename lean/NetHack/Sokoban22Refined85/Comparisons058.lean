/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons057
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8120 (p : Pattern) (guard : d4397 p = 1) : d994 p ≤ (0 : Int) + d1213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d994, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8118 p hg
    simpa only [d4397, d994, d1213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d994, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8119 p hg
    simpa only [d4397, d994, d1213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8121 (p : Pattern) (guard : d4397 p = 1) : d995 p ≤ (0 : Int) + d1214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d995, d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8120 p hg
    simpa only [d995, d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d995, d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8053 p hg
    simpa only [d995, d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8122 (p : Pattern) (guard : d4397 p = 1) : d996 p ≤ (0 : Int) + d1215 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d996, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8116 p hg
    simpa only [d996, d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d996, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8121 p hg
    simpa only [d996, d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8123 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d354 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8124 (p : Pattern) (guard : d4148 p = 1) : d54 p ≤ (0 : Int) + d1154 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d54, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d54, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d54, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8123 p hg
    simpa only [d4148, d54, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8125 (p : Pattern) (guard : d4397 p = 1) : d997 p ≤ (0 : Int) + d1216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d997, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8124 p hg
    simpa only [d4397, d997, d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d997, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7854 p hg
    simpa only [d4397, d997, d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8126 (p : Pattern) (guard : d0 p = 1) : d795 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8127 (p : Pattern) (guard : d4148 p = 1) : d796 p ≤ (0 : Int) + d1181 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d796, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4148, d796, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d796, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8126 p hg
    simpa only [d4148, d796, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8128 (p : Pattern) (guard : d4397 p = 1) : d960 p ≤ (0 : Int) + d1182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d960, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8127 p hg
    simpa only [d4397, d960, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d960, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7815 p hg
    simpa only [d4397, d960, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8129 (p : Pattern) (guard : d4397 p = 1) : d998 p ≤ (0 : Int) + d1217 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d998, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8125 p hg
    simpa only [d998, d1217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d998, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8128 p hg
    simpa only [d998, d1217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8130 (p : Pattern) (guard : d4397 p = 1) : d960 p ≤ (0 : Int) + d1218 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d960, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8127 p hg
    simpa only [d4397, d960, d1218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d960, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7802 p hg
    simpa only [d4397, d960, d1218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8131 (p : Pattern) (guard : d4397 p = 1) : d962 p ≤ (0 : Int) + d1219 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d962, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8130 p hg
    simpa only [d962, d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d962, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8069 p hg
    simpa only [d962, d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8132 (p : Pattern) (guard : d4397 p = 1) : d999 p ≤ (0 : Int) + d1220 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d999, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8129 p hg
    simpa only [d999, d1220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d999, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8131 p hg
    simpa only [d999, d1220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8133 (p : Pattern) (guard : d4397 p = 1) : d1000 p ≤ (0 : Int) + d1221 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1000, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8122 p hg
    simpa only [d1000, d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1000, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8132 p hg
    simpa only [d1000, d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8134 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1177 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8135 (p : Pattern) (guard : d4397 p = 1) : d1001 p ≤ (0 : Int) + d1222 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1001, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3689 p hg
    simpa only [d4397, d1001, d1222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1001, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8134 p hg
    simpa only [d4397, d1001, d1222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8136 (p : Pattern) (guard : d4397 p = 1) : d1002 p ≤ (0 : Int) + d1223 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1002, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8135 p hg
    simpa only [d1002, d1223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1002, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1002, d1223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8137 (p : Pattern) (guard : d4397 p = 1) : d1003 p ≤ (0 : Int) + d1224 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1003, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8136 p hg
    simpa only [d1003, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1003, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8081 p hg
    simpa only [d1003, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8138 (p : Pattern) (guard : d4397 p = 1) : d966 p ≤ (0 : Int) + d1225 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d966, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8076 p hg
    simpa only [d4397, d966, d1225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d966, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7864 p hg
    simpa only [d4397, d966, d1225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8139 (p : Pattern) (guard : d4397 p = 1) : d1004 p ≤ (0 : Int) + d1226 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1004, d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8138 p hg
    simpa only [d1004, d1226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1004, d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8087 p hg
    simpa only [d1004, d1226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8140 (p : Pattern) (guard : d4397 p = 1) : d1005 p ≤ (0 : Int) + d1227 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1005, d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8139 p hg
    simpa only [d1005, d1227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1005, d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8090 p hg
    simpa only [d1005, d1227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8141 (p : Pattern) (guard : d4397 p = 1) : d1006 p ≤ (0 : Int) + d1228 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1006, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8137 p hg
    simpa only [d1006, d1228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1006, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8140 p hg
    simpa only [d1006, d1228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8142 (p : Pattern) (guard : d4397 p = 1) : d1007 p ≤ (0 : Int) + d1229 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1007, d1229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8133 p hg
    simpa only [d1007, d1229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1007, d1229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8141 p hg
    simpa only [d1007, d1229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8143 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (0 : Int) + d1177 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8144 (p : Pattern) (guard : d4397 p = 1) : d1008 p ≤ (0 : Int) + d1230 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1008, d1230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3697 p hg
    simpa only [d4397, d1008, d1230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1008, d1230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8143 p hg
    simpa only [d4397, d1008, d1230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8145 (p : Pattern) (guard : d4397 p = 1) : d1009 p ≤ (0 : Int) + d1231 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1009, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8144 p hg
    simpa only [d1009, d1231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1009, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1009, d1231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8146 (p : Pattern) (guard : d4397 p = 1) : d1010 p ≤ (0 : Int) + d1232 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1010, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8145 p hg
    simpa only [d1010, d1232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1010, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8081 p hg
    simpa only [d1010, d1232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8147 (p : Pattern) (guard : d4397 p = 1) : d1011 p ≤ (0 : Int) + d1233 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1011, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8146 p hg
    simpa only [d1011, d1233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1011, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8140 p hg
    simpa only [d1011, d1233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8148 (p : Pattern) (guard : d4397 p = 1) : d1012 p ≤ (0 : Int) + d1234 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1012, d1234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8147 p hg
    simpa only [d1012, d1234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1012, d1234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1012, d1234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8149 (p : Pattern) (guard : d4397 p = 1) : d1013 p ≤ (0 : Int) + d1235 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1013, d1235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8142 p hg
    simpa only [d1013, d1235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1013, d1235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8148 p hg
    simpa only [d1013, d1235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8150 (p : Pattern) (guard : d4397 p = 1) : d1014 p ≤ (0 : Int) + d1236 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1014, d1236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8110 p hg
    simpa only [d1014, d1236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1014, d1236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8149 p hg
    simpa only [d1014, d1236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8151 (p : Pattern) (guard : d0 p = 1) : d355 p ≤ (0 : Int) + d1154 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8152 (p : Pattern) (guard : d4397 p = 1) : d1015 p ≤ (0 : Int) + d1238 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1015, d1238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3708 p hg
    simpa only [d4397, d1015, d1238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1015, d1238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8151 p hg
    simpa only [d4397, d1015, d1238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8153 (p : Pattern) (guard : d4148 p = 1) : d950 p ≤ (0 : Int) + d1197 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d950, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d950, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d950, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8049 p hg
    simpa only [d4148, d950, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8154 (p : Pattern) (guard : d4397 p = 1) : d1016 p ≤ (0 : Int) + d1239 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1016, d1239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8153 p hg
    simpa only [d4397, d1016, d1239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1016, d1239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7880 p hg
    simpa only [d4397, d1016, d1239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8155 (p : Pattern) (guard : d4397 p = 1) : d1017 p ≤ (0 : Int) + d1240 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1017, d1240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8152 p hg
    simpa only [d1017, d1240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1017, d1240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8154 p hg
    simpa only [d1017, d1240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8156 (p : Pattern) (guard : d0 p = 1) : d33 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8157 (p : Pattern) (guard : d4148 p = 1) : d33 p ≤ (0 : Int) + d1241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4148, d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8156 p hg
    simpa only [d4148, d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8158 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (0 : Int) + d1158 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8159 (p : Pattern) (guard : d4397 p = 1) : d1018 p ≤ (0 : Int) + d1242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1018, d1242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8157 p hg
    simpa only [d4397, d1018, d1242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1018, d1242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8158 p hg
    simpa only [d4397, d1018, d1242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8160 (p : Pattern) (guard : d4397 p = 1) : d1019 p ≤ (0 : Int) + d1243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1019, d1243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8159 p hg
    simpa only [d1019, d1243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1019, d1243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8053 p hg
    simpa only [d1019, d1243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8161 (p : Pattern) (guard : d4397 p = 1) : d1020 p ≤ (0 : Int) + d1244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1020, d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8155 p hg
    simpa only [d1020, d1244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1020, d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8160 p hg
    simpa only [d1020, d1244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8162 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d368 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8163 (p : Pattern) (guard : d4148 p = 1) : d54 p ≤ (0 : Int) + d1208 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d54, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d54, d1208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d54, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8162 p hg
    simpa only [d4148, d54, d1208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8164 (p : Pattern) (guard : d4397 p = 1) : d1021 p ≤ (0 : Int) + d1245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1021, d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8163 p hg
    simpa only [d4397, d1021, d1245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1021, d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7887 p hg
    simpa only [d4397, d1021, d1245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8165 (p : Pattern) (guard : d4397 p = 1) : d960 p ≤ (0 : Int) + d1246 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d960, d1246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8064 p hg
    simpa only [d4397, d960, d1246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d960, d1246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7815 p hg
    simpa only [d4397, d960, d1246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8166 (p : Pattern) (guard : d4397 p = 1) : d1022 p ≤ (0 : Int) + d1247 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1022, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8164 p hg
    simpa only [d1022, d1247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1022, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8165 p hg
    simpa only [d1022, d1247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8167 (p : Pattern) (guard : d4397 p = 1) : d1023 p ≤ (0 : Int) + d1248 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1023, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8166 p hg
    simpa only [d1023, d1248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1023, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8131 p hg
    simpa only [d1023, d1248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8168 (p : Pattern) (guard : d4397 p = 1) : d1024 p ≤ (0 : Int) + d1249 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1024, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8161 p hg
    simpa only [d1024, d1249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1024, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8167 p hg
    simpa only [d1024, d1249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8169 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (0 : Int) + d1177 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8170 (p : Pattern) (guard : d4397 p = 1) : d1025 p ≤ (0 : Int) + d1250 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1025, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3722 p hg
    simpa only [d4397, d1025, d1250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1025, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8169 p hg
    simpa only [d4397, d1025, d1250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8171 (p : Pattern) (guard : d4397 p = 1) : d1026 p ≤ (0 : Int) + d1251 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1026, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8170 p hg
    simpa only [d1026, d1251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1026, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1026, d1251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8172 (p : Pattern) (guard : d4397 p = 1) : d1027 p ≤ (0 : Int) + d1252 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1027, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8171 p hg
    simpa only [d1027, d1252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1027, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8081 p hg
    simpa only [d1027, d1252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8173 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8174 (p : Pattern) (guard : d4148 p = 1) : d54 p ≤ (0 : Int) + d1193 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d54, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d54, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d54, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8173 p hg
    simpa only [d4148, d54, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8175 (p : Pattern) (guard : d4397 p = 1) : d966 p ≤ (0 : Int) + d1253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d966, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8174 p hg
    simpa only [d4397, d966, d1253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d966, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7864 p hg
    simpa only [d4397, d966, d1253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8176 (p : Pattern) (guard : d4397 p = 1) : d1004 p ≤ (0 : Int) + d1254 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1004, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8175 p hg
    simpa only [d1004, d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1004, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8087 p hg
    simpa only [d1004, d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8177 (p : Pattern) (guard : d4397 p = 1) : d1005 p ≤ (0 : Int) + d1255 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1005, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8176 p hg
    simpa only [d1005, d1255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1005, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8090 p hg
    simpa only [d1005, d1255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8178 (p : Pattern) (guard : d4397 p = 1) : d1028 p ≤ (0 : Int) + d1256 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1028, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8172 p hg
    simpa only [d1028, d1256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1028, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8177 p hg
    simpa only [d1028, d1256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8179 (p : Pattern) (guard : d4397 p = 1) : d1029 p ≤ (0 : Int) + d1257 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1029, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8168 p hg
    simpa only [d1029, d1257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1029, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8178 p hg
    simpa only [d1029, d1257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8180 (p : Pattern) (guard : d4397 p = 1) : d1030 p ≤ (0 : Int) + d1258 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1030, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d1030, d1258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1030, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8108 p hg
    simpa only [d1030, d1258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8181 (p : Pattern) (guard : d4397 p = 1) : d1031 p ≤ (0 : Int) + d1259 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1031, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8179 p hg
    simpa only [d1031, d1259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1031, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8180 p hg
    simpa only [d1031, d1259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8182 (p : Pattern) (guard : d4148 p = 1) : d950 p ≤ (0 : Int) + d1177 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d950, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d950, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d950, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8117 p hg
    simpa only [d4148, d950, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8183 (p : Pattern) (guard : d4397 p = 1) : d992 p ≤ (0 : Int) + d1179 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d992, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8182 p hg
    simpa only [d4397, d992, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d992, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7812 p hg
    simpa only [d4397, d992, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8184 (p : Pattern) (guard : d4397 p = 1) : d1032 p ≤ (0 : Int) + d1195 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1032, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8095 p hg
    simpa only [d1032, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1032, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8183 p hg
    simpa only [d1032, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8185 (p : Pattern) (guard : d4397 p = 1) : d1033 p ≤ (0 : Int) + d1260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1033, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8184 p hg
    simpa only [d1033, d1260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1033, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8121 p hg
    simpa only [d1033, d1260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8186 (p : Pattern) (guard : d4397 p = 1) : d1034 p ≤ (0 : Int) + d1199 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1034, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d1034, d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1034, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8128 p hg
    simpa only [d1034, d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8187 (p : Pattern) (guard : d4397 p = 1) : d1035 p ≤ (0 : Int) + d1261 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1035, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8186 p hg
    simpa only [d1035, d1261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1035, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8131 p hg
    simpa only [d1035, d1261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8188 (p : Pattern) (guard : d4397 p = 1) : d1036 p ≤ (0 : Int) + d1262 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1036, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8185 p hg
    simpa only [d1036, d1262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1036, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8187 p hg
    simpa only [d1036, d1262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8189 (p : Pattern) (guard : d4397 p = 1) : d1001 p ≤ (0 : Int) + d1177 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3736 p hg
    simpa only [d4397, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8134 p hg
    simpa only [d4397, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8190 (p : Pattern) (guard : d4397 p = 1) : d1002 p ≤ (0 : Int) + d1263 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1002, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8189 p hg
    simpa only [d1002, d1263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1002, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1002, d1263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8191 (p : Pattern) (guard : d4397 p = 1) : d1003 p ≤ (0 : Int) + d1264 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1003, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8190 p hg
    simpa only [d1003, d1264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1003, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8081 p hg
    simpa only [d1003, d1264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8192 (p : Pattern) (guard : d4397 p = 1) : d1006 p ≤ (0 : Int) + d1265 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1006, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8191 p hg
    simpa only [d1006, d1265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1006, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8140 p hg
    simpa only [d1006, d1265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8193 (p : Pattern) (guard : d4397 p = 1) : d1037 p ≤ (0 : Int) + d1266 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1037, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8188 p hg
    simpa only [d1037, d1266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1037, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8192 p hg
    simpa only [d1037, d1266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8194 (p : Pattern) (guard : d4397 p = 1) : d1038 p ≤ (0 : Int) + d1267 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1038, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8141 p hg
    simpa only [d1038, d1267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1038, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1038, d1267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8195 (p : Pattern) (guard : d4397 p = 1) : d1039 p ≤ (0 : Int) + d1268 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1039, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8193 p hg
    simpa only [d1039, d1268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1039, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8194 p hg
    simpa only [d1039, d1268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8196 (p : Pattern) (guard : d4397 p = 1) : d1040 p ≤ (0 : Int) + d1269 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1040, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8181 p hg
    simpa only [d1040, d1269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1040, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8195 p hg
    simpa only [d1040, d1269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8197 (p : Pattern) (guard : d4397 p = 1) : d1041 p ≤ (0 : Int) + d1270 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1041, d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8150 p hg
    simpa only [d1041, d1270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1041, d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8196 p hg
    simpa only [d1041, d1270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8198 (p : Pattern) (guard : d0 p = 1) : d355 p ≤ (0 : Int) + d1272 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8199 (p : Pattern) (guard : d4397 p = 1) : d1042 p ≤ (0 : Int) + d1273 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1042, d1273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3748 p hg
    simpa only [d4397, d1042, d1273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1042, d1273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8198 p hg
    simpa only [d4397, d1042, d1273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8200 (p : Pattern) (guard : d0 p = 1) : d118 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8201 (p : Pattern) (guard : d4148 p = 1) : d1043 p ≤ (0 : Int) + d1274 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1043, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1043, d1274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1043, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8200 p hg
    simpa only [d4148, d1043, d1274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8202 (p : Pattern) (guard : d4397 p = 1) : d1044 p ≤ (0 : Int) + d1275 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1044, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8201 p hg
    simpa only [d4397, d1044, d1275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1044, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7913 p hg
    simpa only [d4397, d1044, d1275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8203 (p : Pattern) (guard : d4397 p = 1) : d1045 p ≤ (0 : Int) + d1276 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1045, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8199 p hg
    simpa only [d1045, d1276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1045, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8202 p hg
    simpa only [d1045, d1276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8204 (p : Pattern) (guard : d0 p = 1) : d118 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8205 (p : Pattern) (guard : d4148 p = 1) : d118 p ≤ (0 : Int) + d1277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4148, d1277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8204 p hg
    simpa only [d4148, d1277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8206 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (0 : Int) + d1278 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8207 (p : Pattern) (guard : d4397 p = 1) : d1046 p ≤ (0 : Int) + d1279 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1046, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8205 p hg
    simpa only [d4397, d1046, d1279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1046, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8206 p hg
    simpa only [d4397, d1046, d1279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8208 (p : Pattern) (guard : d4397 p = 1) : d1047 p ≤ (0 : Int) + d1280 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1047, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3762 p hg
    simpa only [d4397, d1047, d1280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1047, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7919 p hg
    simpa only [d4397, d1047, d1280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8209 (p : Pattern) (guard : d4397 p = 1) : d1048 p ≤ (0 : Int) + d1281 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1048, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8207 p hg
    simpa only [d1048, d1281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1048, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8208 p hg
    simpa only [d1048, d1281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8210 (p : Pattern) (guard : d4397 p = 1) : d1049 p ≤ (0 : Int) + d1282 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1049, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8203 p hg
    simpa only [d1049, d1282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1049, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8209 p hg
    simpa only [d1049, d1282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8211 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (0 : Int) + d368 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8212 (p : Pattern) (guard : d4148 p = 1) : d133 p ≤ (0 : Int) + d1283 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d133, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d133, d1283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d133, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8211 p hg
    simpa only [d4148, d133, d1283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8213 (p : Pattern) (guard : d4397 p = 1) : d1050 p ≤ (0 : Int) + d1285 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1050, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8212 p hg
    simpa only [d4397, d1050, d1285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1050, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7923 p hg
    simpa only [d4397, d1050, d1285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8214 (p : Pattern) (guard : d0 p = 1) : d861 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8215 (p : Pattern) (guard : d4148 p = 1) : d862 p ≤ (0 : Int) + d1286 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d862, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4148, d862, d1286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d862, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8214 p hg
    simpa only [d4148, d862, d1286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8216 (p : Pattern) (guard : d4397 p = 1) : d1051 p ≤ (0 : Int) + d1287 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1051, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8215 p hg
    simpa only [d4397, d1051, d1287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1051, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1051, d1287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8217 (p : Pattern) (guard : d4397 p = 1) : d1052 p ≤ (0 : Int) + d1288 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1052, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8213 p hg
    simpa only [d1052, d1288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1052, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8216 p hg
    simpa only [d1052, d1288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8218 (p : Pattern) (guard : d0 p = 1) : d861 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8219 (p : Pattern) (guard : d4148 p = 1) : d862 p ≤ (0 : Int) + d1289 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d862, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4148, d862, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d862, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8218 p hg
    simpa only [d4148, d862, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8220 (p : Pattern) (guard : d4397 p = 1) : d1051 p ≤ (0 : Int) + d1291 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1051, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8219 p hg
    simpa only [d4397, d1051, d1291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1051, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7927 p hg
    simpa only [d4397, d1051, d1291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8221 (p : Pattern) (guard : d1 p = 1) : d139 p ≤ (0 : Int) + d139 p := by
  omega
theorem compare8222 (p : Pattern) (guard : d0 p = 1) : d229 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8223 (p : Pattern) (guard : d4148 p = 1) : d1053 p ≤ (0 : Int) + d1290 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1053, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8221 p hg
    simpa only [d4148, d1053, d1290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1053, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8222 p hg
    simpa only [d4148, d1053, d1290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8224 (p : Pattern) (guard : d4397 p = 1) : d1054 p ≤ (0 : Int) + d1292 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1054, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8223 p hg
    simpa only [d4397, d1054, d1292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1054, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1054, d1292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8225 (p : Pattern) (guard : d4397 p = 1) : d1055 p ≤ (0 : Int) + d1293 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1055, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8220 p hg
    simpa only [d1055, d1293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1055, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8224 p hg
    simpa only [d1055, d1293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8226 (p : Pattern) (guard : d4397 p = 1) : d1056 p ≤ (0 : Int) + d1294 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1056, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8217 p hg
    simpa only [d1056, d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1056, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8225 p hg
    simpa only [d1056, d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8227 (p : Pattern) (guard : d4397 p = 1) : d1057 p ≤ (0 : Int) + d1295 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1057, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8210 p hg
    simpa only [d1057, d1295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1057, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8226 p hg
    simpa only [d1057, d1295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8228 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (0 : Int) + d1296 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8229 (p : Pattern) (guard : d4397 p = 1) : d1058 p ≤ (0 : Int) + d1297 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1058, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3771 p hg
    simpa only [d4397, d1058, d1297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1058, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8228 p hg
    simpa only [d4397, d1058, d1297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8230 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8231 (p : Pattern) (guard : d4148 p = 1) : d133 p ≤ (0 : Int) + d1296 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d133, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d133, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d133, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8230 p hg
    simpa only [d4148, d133, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8232 (p : Pattern) (guard : d4397 p = 1) : d1059 p ≤ (0 : Int) + d1298 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1059, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8231 p hg
    simpa only [d4397, d1059, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1059, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d4397, d1059, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8233 (p : Pattern) (guard : d4397 p = 1) : d1060 p ≤ (0 : Int) + d1299 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1060, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8229 p hg
    simpa only [d1060, d1299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1060, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8232 p hg
    simpa only [d1060, d1299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8234 (p : Pattern) (guard : d4148 p = 1) : d132 p ≤ (0 : Int) + d1289 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4148, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8230 p hg
    simpa only [d4148, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8235 (p : Pattern) (guard : d4397 p = 1) : d1061 p ≤ (0 : Int) + d1300 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1061, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8234 p hg
    simpa only [d4397, d1061, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1061, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1061, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8236 (p : Pattern) (guard : d4397 p = 1) : d1062 p ≤ (0 : Int) + d1301 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1062, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8235 p hg
    simpa only [d1062, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1062, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1062, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8237 (p : Pattern) (guard : d4397 p = 1) : d1063 p ≤ (0 : Int) + d1302 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1063, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8233 p hg
    simpa only [d1063, d1302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1063, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8236 p hg
    simpa only [d1063, d1302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8238 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8239 (p : Pattern) (guard : d4148 p = 1) : d133 p ≤ (0 : Int) + d1303 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d133, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d133, d1303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d133, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8238 p hg
    simpa only [d4148, d133, d1303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8240 (p : Pattern) (guard : d4397 p = 1) : d1059 p ≤ (0 : Int) + d1304 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1059, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8239 p hg
    simpa only [d4397, d1059, d1304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1059, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7940 p hg
    simpa only [d4397, d1059, d1304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8241 (p : Pattern) (guard : d4148 p = 1) : d873 p ≤ (0 : Int) + d1289 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d873, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4148, d873, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d873, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3772 p hg
    simpa only [d4148, d873, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8242 (p : Pattern) (guard : d4397 p = 1) : d1064 p ≤ (0 : Int) + d1300 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1064, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8241 p hg
    simpa only [d4397, d1064, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1064, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1064, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8243 (p : Pattern) (guard : d4397 p = 1) : d1065 p ≤ (0 : Int) + d1305 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1065, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8240 p hg
    simpa only [d1065, d1305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1065, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8242 p hg
    simpa only [d1065, d1305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8244 (p : Pattern) (guard : d4397 p = 1) : d1066 p ≤ (0 : Int) + d1301 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1066, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8242 p hg
    simpa only [d1066, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1066, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1066, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8245 (p : Pattern) (guard : d4397 p = 1) : d1067 p ≤ (0 : Int) + d1306 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1067, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8243 p hg
    simpa only [d1067, d1306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1067, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8244 p hg
    simpa only [d1067, d1306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8246 (p : Pattern) (guard : d4397 p = 1) : d1068 p ≤ (0 : Int) + d1307 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1068, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8237 p hg
    simpa only [d1068, d1307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1068, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8245 p hg
    simpa only [d1068, d1307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8247 (p : Pattern) (guard : d4397 p = 1) : d1069 p ≤ (0 : Int) + d1308 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1069, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8227 p hg
    simpa only [d1069, d1308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1069, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8246 p hg
    simpa only [d1069, d1308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8248 (p : Pattern) (guard : d0 p = 1) : d361 p ≤ (0 : Int) + d1296 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8249 (p : Pattern) (guard : d4397 p = 1) : d1070 p ≤ (0 : Int) + d1309 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1070, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3786 p hg
    simpa only [d4397, d1070, d1309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1070, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8248 p hg
    simpa only [d4397, d1070, d1309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8250 (p : Pattern) (guard : d4397 p = 1) : d1071 p ≤ (0 : Int) + d1310 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1071, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8249 p hg
    simpa only [d1071, d1310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1071, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8232 p hg
    simpa only [d1071, d1310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8251 (p : Pattern) (guard : d4397 p = 1) : d1072 p ≤ (0 : Int) + d1311 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1072, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8250 p hg
    simpa only [d1072, d1311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1072, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8236 p hg
    simpa only [d1072, d1311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8252 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8253 (p : Pattern) (guard : d4148 p = 1) : d133 p ≤ (0 : Int) + d1312 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d133, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d133, d1312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d133, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8252 p hg
    simpa only [d4148, d133, d1312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8254 (p : Pattern) (guard : d4397 p = 1) : d1073 p ≤ (0 : Int) + d1313 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1073, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8253 p hg
    simpa only [d4397, d1073, d1313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1073, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7952 p hg
    simpa only [d4397, d1073, d1313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8255 (p : Pattern) (guard : d4397 p = 1) : d1074 p ≤ (0 : Int) + d1314 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1074, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8254 p hg
    simpa only [d1074, d1314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1074, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8242 p hg
    simpa only [d1074, d1314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8256 (p : Pattern) (guard : d4397 p = 1) : d1075 p ≤ (0 : Int) + d1315 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1075, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8255 p hg
    simpa only [d1075, d1315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1075, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8244 p hg
    simpa only [d1075, d1315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8257 (p : Pattern) (guard : d4397 p = 1) : d1076 p ≤ (0 : Int) + d1316 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1076, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8251 p hg
    simpa only [d1076, d1316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1076, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8256 p hg
    simpa only [d1076, d1316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8258 (p : Pattern) (guard : d4397 p = 1) : d162 p ≤ (0 : Int) + d162 p := by
  omega
theorem compare8259 (p : Pattern) (guard : d4397 p = 1) : d1077 p ≤ (0 : Int) + d1317 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1077, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8257 p hg
    simpa only [d1077, d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1077, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8258 p hg
    simpa only [d1077, d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
