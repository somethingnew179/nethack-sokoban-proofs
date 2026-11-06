/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons349
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare49000 (p : Pattern) (guard : d8107 p = 1) : d1272 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1272, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35127 p hg
    simpa only [d8107, d1272, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1272, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48977 p hg
    simpa only [d8107, d1272, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49001 (p : Pattern) (guard : d8108 p = 1) : d1273 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1273, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48999 p hg
    simpa only [d8108, d1273, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1273, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49000 p hg
    simpa only [d8108, d1273, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49002 (p : Pattern) (guard : d8107 p = 1) : d1274 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1274, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35149 p hg
    simpa only [d8107, d1274, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1274, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47893 p hg
    simpa only [d8107, d1274, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49003 (p : Pattern) (guard : d8113 p = 1) : d1275 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1275, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49002 p hg
    simpa only [d8113, d1275, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1275, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35157 p hg
    simpa only [d8113, d1275, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49004 (p : Pattern) (guard : d8114 p = 1) : d1276 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1276, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49001 p hg
    simpa only [d8114, d1276, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1276, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49003 p hg
    simpa only [d8114, d1276, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49005 (p : Pattern) (guard : d8107 p = 1) : d1277 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1277, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35173 p hg
    simpa only [d8107, d1277, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1277, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47804 p hg
    simpa only [d8107, d1277, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49006 (p : Pattern) (guard : d8112 p = 1) : d1278 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1278, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35188 p hg
    simpa only [d8112, d1278, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1278, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1278, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49007 (p : Pattern) (guard : d8113 p = 1) : d1279 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1279, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49005 p hg
    simpa only [d8113, d1279, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1279, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49006 p hg
    simpa only [d8113, d1279, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49008 (p : Pattern) (guard : d8112 p = 1) : d1278 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35194 p hg
    simpa only [d8112, d1278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49009 (p : Pattern) (guard : d8118 p = 1) : d1280 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49008 p hg
    simpa only [d8118, d1280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35196 p hg
    simpa only [d8118, d1280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49010 (p : Pattern) (guard : d8119 p = 1) : d1281 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1281, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49007 p hg
    simpa only [d8119, d1281, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1281, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49009 p hg
    simpa only [d8119, d1281, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49011 (p : Pattern) (guard : d8120 p = 1) : d1282 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1282, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49004 p hg
    simpa only [d8120, d1282, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1282, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49010 p hg
    simpa only [d8120, d1282, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49012 (p : Pattern) (guard : d8106 p = 1) : d368 p ≤ (0 : Int) + d368 p := by
  omega
theorem compare49013 (p : Pattern) (guard : d8107 p = 1) : d1283 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1283, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35206 p hg
    simpa only [d8107, d1283, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1283, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49012 p hg
    simpa only [d8107, d1283, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49014 (p : Pattern) (guard : d8113 p = 1) : d1285 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1285, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49013 p hg
    simpa only [d8113, d1285, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1285, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47960 p hg
    simpa only [d8113, d1285, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49015 (p : Pattern) (guard : d8111 p = 1) : d373 p ≤ (0 : Int) + d373 p := by
  omega
theorem compare49016 (p : Pattern) (guard : d8112 p = 1) : d1286 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1286, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47968 p hg
    simpa only [d8112, d1286, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1286, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49015 p hg
    simpa only [d8112, d1286, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49017 (p : Pattern) (guard : d8118 p = 1) : d1287 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1287, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49016 p hg
    simpa only [d8118, d1287, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1287, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1287, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49018 (p : Pattern) (guard : d8119 p = 1) : d1288 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1288, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49014 p hg
    simpa only [d8119, d1288, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1288, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49017 p hg
    simpa only [d8119, d1288, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49019 (p : Pattern) (guard : d8112 p = 1) : d1289 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1289, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47978 p hg
    simpa only [d8112, d1289, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1289, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1289, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49020 (p : Pattern) (guard : d8118 p = 1) : d1291 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1291, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49019 p hg
    simpa only [d8118, d1291, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1291, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47981 p hg
    simpa only [d8118, d1291, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49021 (p : Pattern) (guard : d8123 p = 1) : d1292 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47981 p hg
    simpa only [d8123, d1292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49022 (p : Pattern) (guard : d8124 p = 1) : d1293 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1293, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49020 p hg
    simpa only [d8124, d1293, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1293, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49021 p hg
    simpa only [d8124, d1293, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49023 (p : Pattern) (guard : d8125 p = 1) : d1294 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1294, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49018 p hg
    simpa only [d8125, d1294, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1294, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49022 p hg
    simpa only [d8125, d1294, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49024 (p : Pattern) (guard : d8126 p = 1) : d1295 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1295, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49011 p hg
    simpa only [d8126, d1295, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1295, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49023 p hg
    simpa only [d8126, d1295, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49025 (p : Pattern) (guard : d8112 p = 1) : d1296 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1296, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35255 p hg
    simpa only [d8112, d1296, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1296, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1296, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49026 (p : Pattern) (guard : d8113 p = 1) : d1297 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1297, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49002 p hg
    simpa only [d8113, d1297, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1297, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49025 p hg
    simpa only [d8113, d1297, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49027 (p : Pattern) (guard : d8112 p = 1) : d1296 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1296, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35259 p hg
    simpa only [d8112, d1296, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1296, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1296, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49028 (p : Pattern) (guard : d8118 p = 1) : d1298 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1298, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49027 p hg
    simpa only [d8118, d1298, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1298, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35261 p hg
    simpa only [d8118, d1298, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49029 (p : Pattern) (guard : d8119 p = 1) : d1299 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1299, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49026 p hg
    simpa only [d8119, d1299, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1299, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49028 p hg
    simpa only [d8119, d1299, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49030 (p : Pattern) (guard : d8112 p = 1) : d1289 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35265 p hg
    simpa only [d8112, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49031 (p : Pattern) (guard : d8118 p = 1) : d1300 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49030 p hg
    simpa only [d8118, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49032 (p : Pattern) (guard : d8124 p = 1) : d1301 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49031 p hg
    simpa only [d8124, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49033 (p : Pattern) (guard : d8125 p = 1) : d1302 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1302, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49029 p hg
    simpa only [d8125, d1302, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1302, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49032 p hg
    simpa only [d8125, d1302, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49034 (p : Pattern) (guard : d8112 p = 1) : d1303 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1303, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35276 p hg
    simpa only [d8112, d1303, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1303, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49015 p hg
    simpa only [d8112, d1303, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49035 (p : Pattern) (guard : d8118 p = 1) : d1304 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1304, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49034 p hg
    simpa only [d8118, d1304, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1304, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47993 p hg
    simpa only [d8118, d1304, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49036 (p : Pattern) (guard : d8123 p = 1) : d1300 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47993 p hg
    simpa only [d8123, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49037 (p : Pattern) (guard : d8124 p = 1) : d1305 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1305, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49035 p hg
    simpa only [d8124, d1305, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1305, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49036 p hg
    simpa only [d8124, d1305, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49038 (p : Pattern) (guard : d8129 p = 1) : d1301 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49036 p hg
    simpa only [d8129, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49039 (p : Pattern) (guard : d8130 p = 1) : d1306 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1306, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49037 p hg
    simpa only [d8130, d1306, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1306, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49038 p hg
    simpa only [d8130, d1306, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49040 (p : Pattern) (guard : d8131 p = 1) : d1307 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1307, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49033 p hg
    simpa only [d8131, d1307, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1307, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49039 p hg
    simpa only [d8131, d1307, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49041 (p : Pattern) (guard : d8132 p = 1) : d1308 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1308, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49024 p hg
    simpa only [d8132, d1308, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1308, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49040 p hg
    simpa only [d8132, d1308, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49042 (p : Pattern) (guard : d8112 p = 1) : d1296 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1296, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35253 p hg
    simpa only [d8112, d1296, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1296, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1296, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49043 (p : Pattern) (guard : d8113 p = 1) : d1309 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1309, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49000 p hg
    simpa only [d8113, d1309, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1309, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49042 p hg
    simpa only [d8113, d1309, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49044 (p : Pattern) (guard : d8118 p = 1) : d1298 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1298, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49025 p hg
    simpa only [d8118, d1298, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1298, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35261 p hg
    simpa only [d8118, d1298, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49045 (p : Pattern) (guard : d8119 p = 1) : d1310 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1310, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49043 p hg
    simpa only [d8119, d1310, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1310, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49044 p hg
    simpa only [d8119, d1310, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49046 (p : Pattern) (guard : d8112 p = 1) : d1289 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1289, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38210 p hg
    simpa only [d8112, d1289, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1289, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1289, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49047 (p : Pattern) (guard : d8118 p = 1) : d1300 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1300, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49046 p hg
    simpa only [d8118, d1300, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1300, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1300, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49048 (p : Pattern) (guard : d8124 p = 1) : d1301 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1301, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49047 p hg
    simpa only [d8124, d1301, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1301, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1301, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49049 (p : Pattern) (guard : d8125 p = 1) : d1311 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1311, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49045 p hg
    simpa only [d8125, d1311, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1311, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49048 p hg
    simpa only [d8125, d1311, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49050 (p : Pattern) (guard : d8112 p = 1) : d1312 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1312, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35302 p hg
    simpa only [d8112, d1312, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1312, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47959 p hg
    simpa only [d8112, d1312, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49051 (p : Pattern) (guard : d8118 p = 1) : d1313 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1313, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49050 p hg
    simpa only [d8118, d1313, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1313, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48009 p hg
    simpa only [d8118, d1313, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49052 (p : Pattern) (guard : d8124 p = 1) : d1314 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1314, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49051 p hg
    simpa only [d8124, d1314, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1314, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49036 p hg
    simpa only [d8124, d1314, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49053 (p : Pattern) (guard : d8130 p = 1) : d1315 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1315, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49052 p hg
    simpa only [d8130, d1315, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1315, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49038 p hg
    simpa only [d8130, d1315, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49054 (p : Pattern) (guard : d8131 p = 1) : d1316 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1316, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49049 p hg
    simpa only [d8131, d1316, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1316, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49053 p hg
    simpa only [d8131, d1316, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49055 (p : Pattern) (guard : d8137 p = 1) : d1317 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1317, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49054 p hg
    simpa only [d8137, d1317, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1317, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38220 p hg
    simpa only [d8137, d1317, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49056 (p : Pattern) (guard : d8138 p = 1) : d1318 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1318, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49041 p hg
    simpa only [d8138, d1318, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1318, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49055 p hg
    simpa only [d8138, d1318, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49057 (p : Pattern) (guard : d8106 p = 1) : d345 p ≤ (0 : Int) + d345 p := by
  omega
theorem compare49058 (p : Pattern) (guard : d8107 p = 1) : d1319 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1319, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35119 p hg
    simpa only [d8107, d1319, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1319, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49057 p hg
    simpa only [d8107, d1319, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49059 (p : Pattern) (guard : d8113 p = 1) : d1320 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1320, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49058 p hg
    simpa only [d8113, d1320, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1320, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49034 p hg
    simpa only [d8113, d1320, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49060 (p : Pattern) (guard : d8118 p = 1) : d1298 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1298, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49042 p hg
    simpa only [d8118, d1298, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1298, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35261 p hg
    simpa only [d8118, d1298, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49061 (p : Pattern) (guard : d8119 p = 1) : d1321 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1321, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49059 p hg
    simpa only [d8119, d1321, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1321, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49060 p hg
    simpa only [d8119, d1321, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49062 (p : Pattern) (guard : d8112 p = 1) : d1322 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1322, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35315 p hg
    simpa only [d8112, d1322, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1322, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1322, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49063 (p : Pattern) (guard : d8117 p = 1) : d1278 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35319 p hg
    simpa only [d8117, d1278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49064 (p : Pattern) (guard : d8118 p = 1) : d1323 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1323, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49062 p hg
    simpa only [d8118, d1323, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1323, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49063 p hg
    simpa only [d8118, d1323, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49065 (p : Pattern) (guard : d8123 p = 1) : d1280 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49063 p hg
    simpa only [d8123, d1280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4322 p hg
    simpa only [d8123, d1280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49066 (p : Pattern) (guard : d8124 p = 1) : d1324 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1324, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49064 p hg
    simpa only [d8124, d1324, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1324, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49065 p hg
    simpa only [d8124, d1324, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49067 (p : Pattern) (guard : d8125 p = 1) : d1325 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1325, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49061 p hg
    simpa only [d8125, d1325, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1325, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49066 p hg
    simpa only [d8125, d1325, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49068 (p : Pattern) (guard : d8112 p = 1) : d1274 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1274, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35329 p hg
    simpa only [d8112, d1274, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1274, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48151 p hg
    simpa only [d8112, d1274, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49069 (p : Pattern) (guard : d8118 p = 1) : d1326 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1326, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49068 p hg
    simpa only [d8118, d1326, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1326, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48024 p hg
    simpa only [d8118, d1326, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49070 (p : Pattern) (guard : d8123 p = 1) : d1300 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1300, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48009 p hg
    simpa only [d8123, d1300, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1300, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1300, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49071 (p : Pattern) (guard : d8124 p = 1) : d1327 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1327, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49069 p hg
    simpa only [d8124, d1327, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1327, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49070 p hg
    simpa only [d8124, d1327, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49072 (p : Pattern) (guard : d8123 p = 1) : d1291 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47993 p hg
    simpa only [d8123, d1291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10219 p hg
    simpa only [d8123, d1291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49073 (p : Pattern) (guard : d0 p = 1) : d1292 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49074 (p : Pattern) (guard : d8129 p = 1) : d1293 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49072 p hg
    simpa only [d8129, d1293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49073 p hg
    simpa only [d8129, d1293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49075 (p : Pattern) (guard : d8130 p = 1) : d1328 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1328, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49071 p hg
    simpa only [d8130, d1328, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1328, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49074 p hg
    simpa only [d8130, d1328, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49076 (p : Pattern) (guard : d8131 p = 1) : d1329 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1329, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49067 p hg
    simpa only [d8131, d1329, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1329, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49075 p hg
    simpa only [d8131, d1329, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49077 (p : Pattern) (guard : d8117 p = 1) : d1296 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35354 p hg
    simpa only [d8117, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49078 (p : Pattern) (guard : d8118 p = 1) : d1296 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49042 p hg
    simpa only [d8118, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49077 p hg
    simpa only [d8118, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49079 (p : Pattern) (guard : d8123 p = 1) : d1298 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49077 p hg
    simpa only [d8123, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d8123, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49080 (p : Pattern) (guard : d8124 p = 1) : d1330 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1330, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49078 p hg
    simpa only [d8124, d1330, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1330, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49079 p hg
    simpa only [d8124, d1330, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49081 (p : Pattern) (guard : d8130 p = 1) : d1331 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1331, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49080 p hg
    simpa only [d8130, d1331, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1331, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49038 p hg
    simpa only [d8130, d1331, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49082 (p : Pattern) (guard : d8117 p = 1) : d1296 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1296, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35370 p hg
    simpa only [d8117, d1296, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1296, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1296, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49083 (p : Pattern) (guard : d8123 p = 1) : d1332 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1332, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49082 p hg
    simpa only [d8123, d1332, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1332, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10232 p hg
    simpa only [d8123, d1332, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49084 (p : Pattern) (guard : d0 p = 1) : d1300 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49085 (p : Pattern) (guard : d8129 p = 1) : d1333 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1333, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49083 p hg
    simpa only [d8129, d1333, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1333, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49084 p hg
    simpa only [d8129, d1333, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49086 (p : Pattern) (guard : d0 p = 1) : d1301 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49087 (p : Pattern) (guard : d8135 p = 1) : d1334 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1334, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49085 p hg
    simpa only [d8135, d1334, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1334, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49086 p hg
    simpa only [d8135, d1334, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49088 (p : Pattern) (guard : d8136 p = 1) : d1335 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1335, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49081 p hg
    simpa only [d8136, d1335, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1335, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49087 p hg
    simpa only [d8136, d1335, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49089 (p : Pattern) (guard : d8137 p = 1) : d1336 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1336, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49076 p hg
    simpa only [d8137, d1336, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1336, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49088 p hg
    simpa only [d8137, d1336, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49090 (p : Pattern) (guard : d8118 p = 1) : d1337 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1337, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49034 p hg
    simpa only [d8118, d1337, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1337, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49077 p hg
    simpa only [d8118, d1337, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49091 (p : Pattern) (guard : d8124 p = 1) : d1338 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1338, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49090 p hg
    simpa only [d8124, d1338, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1338, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49079 p hg
    simpa only [d8124, d1338, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49092 (p : Pattern) (guard : d8130 p = 1) : d1339 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1339, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49091 p hg
    simpa only [d8130, d1339, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1339, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49038 p hg
    simpa only [d8130, d1339, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49093 (p : Pattern) (guard : d8117 p = 1) : d1296 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1296, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35785 p hg
    simpa only [d8117, d1296, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1296, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1296, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49094 (p : Pattern) (guard : d8123 p = 1) : d1332 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1332, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49093 p hg
    simpa only [d8123, d1332, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1332, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10232 p hg
    simpa only [d8123, d1332, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49095 (p : Pattern) (guard : d8129 p = 1) : d1333 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1333, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49094 p hg
    simpa only [d8129, d1333, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1333, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49084 p hg
    simpa only [d8129, d1333, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49096 (p : Pattern) (guard : d8135 p = 1) : d1334 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1334, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49095 p hg
    simpa only [d8135, d1334, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1334, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49086 p hg
    simpa only [d8135, d1334, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49097 (p : Pattern) (guard : d8136 p = 1) : d1340 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1340, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49092 p hg
    simpa only [d8136, d1340, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1340, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49096 p hg
    simpa only [d8136, d1340, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49098 (p : Pattern) (guard : d8142 p = 1) : d1341 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1341, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49097 p hg
    simpa only [d8142, d1341, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1341, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d1341, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49099 (p : Pattern) (guard : d8143 p = 1) : d1342 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1342, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49089 p hg
    simpa only [d8143, d1342, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1342, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49098 p hg
    simpa only [d8143, d1342, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49100 (p : Pattern) (guard : d8144 p = 1) : d1343 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d1343, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49056 p hg
    simpa only [d8144, d1343, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d1343, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49099 p hg
    simpa only [d8144, d1343, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49101 (p : Pattern) (guard : d8145 p = 1) : d1344 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d1344, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48997 p hg
    simpa only [d8145, d1344, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d1344, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49100 p hg
    simpa only [d8145, d1344, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49102 (p : Pattern) (guard : d8146 p = 1) : d1345 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48937 p hg
    simpa only [d8146, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49101 p hg
    simpa only [d8146, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49103 (p : Pattern) (guard : d8102 p = 1) : d1237 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1237, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35385 p hg
    simpa only [d8102, d1237, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1237, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48998 p hg
    simpa only [d8102, d1237, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49104 (p : Pattern) (guard : d8108 p = 1) : d1238 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1238, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49103 p hg
    simpa only [d8108, d1238, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1238, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48978 p hg
    simpa only [d8108, d1238, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49105 (p : Pattern) (guard : d8113 p = 1) : d1239 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1239, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48902 p hg
    simpa only [d8113, d1239, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1239, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35400 p hg
    simpa only [d8113, d1239, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49106 (p : Pattern) (guard : d8114 p = 1) : d1240 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1240, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49104 p hg
    simpa only [d8114, d1240, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1240, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49105 p hg
    simpa only [d8114, d1240, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49107 (p : Pattern) (guard : d8107 p = 1) : d1241 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1241, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35403 p hg
    simpa only [d8107, d1241, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1241, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47804 p hg
    simpa only [d8107, d1241, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49108 (p : Pattern) (guard : d8112 p = 1) : d1158 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1158, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35406 p hg
    simpa only [d8112, d1158, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1158, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1158, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49109 (p : Pattern) (guard : d8113 p = 1) : d1242 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1242, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49107 p hg
    simpa only [d8113, d1242, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1242, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49108 p hg
    simpa only [d8113, d1242, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49110 (p : Pattern) (guard : d8119 p = 1) : d1243 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1243, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49109 p hg
    simpa only [d8119, d1243, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1243, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48899 p hg
    simpa only [d8119, d1243, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49111 (p : Pattern) (guard : d8120 p = 1) : d1244 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1244, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49106 p hg
    simpa only [d8120, d1244, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1244, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49110 p hg
    simpa only [d8120, d1244, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49112 (p : Pattern) (guard : d8107 p = 1) : d1208 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1208, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35415 p hg
    simpa only [d8107, d1208, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1208, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49012 p hg
    simpa only [d8107, d1208, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49113 (p : Pattern) (guard : d8113 p = 1) : d1245 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1245, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49112 p hg
    simpa only [d8113, d1245, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1245, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48070 p hg
    simpa only [d8113, d1245, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49114 (p : Pattern) (guard : d8112 p = 1) : d1170 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1170, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35047 p hg
    simpa only [d8112, d1170, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1170, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49015 p hg
    simpa only [d8112, d1170, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49115 (p : Pattern) (guard : d8118 p = 1) : d1246 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1246, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49114 p hg
    simpa only [d8118, d1246, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1246, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d1246, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49116 (p : Pattern) (guard : d8119 p = 1) : d1247 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1247, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49113 p hg
    simpa only [d8119, d1247, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1247, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49115 p hg
    simpa only [d8119, d1247, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49117 (p : Pattern) (guard : d8118 p = 1) : d1218 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1218, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47926 p hg
    simpa only [d8118, d1218, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1218, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47853 p hg
    simpa only [d8118, d1218, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49118 (p : Pattern) (guard : d8124 p = 1) : d1219 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1219, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49117 p hg
    simpa only [d8124, d1219, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1219, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48907 p hg
    simpa only [d8124, d1219, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49119 (p : Pattern) (guard : d8125 p = 1) : d1248 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1248, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49116 p hg
    simpa only [d8125, d1248, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1248, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49118 p hg
    simpa only [d8125, d1248, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49120 (p : Pattern) (guard : d8126 p = 1) : d1249 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1249, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49111 p hg
    simpa only [d8126, d1249, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1249, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49119 p hg
    simpa only [d8126, d1249, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49121 (p : Pattern) (guard : d8113 p = 1) : d1250 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1250, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48902 p hg
    simpa only [d8113, d1250, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1250, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48929 p hg
    simpa only [d8113, d1250, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49122 (p : Pattern) (guard : d8118 p = 1) : d1179 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1179, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48917 p hg
    simpa only [d8118, d1179, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1179, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d8118, d1179, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49123 (p : Pattern) (guard : d8119 p = 1) : d1251 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1251, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49121 p hg
    simpa only [d8119, d1251, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1251, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49122 p hg
    simpa only [d8119, d1251, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49124 (p : Pattern) (guard : d8125 p = 1) : d1252 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1252, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49123 p hg
    simpa only [d8125, d1252, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1252, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48915 p hg
    simpa only [d8125, d1252, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49125 (p : Pattern) (guard : d8112 p = 1) : d1193 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1193, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35466 p hg
    simpa only [d8112, d1193, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1193, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49015 p hg
    simpa only [d8112, d1193, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49126 (p : Pattern) (guard : d8118 p = 1) : d1253 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1253, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49125 p hg
    simpa only [d8118, d1253, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1253, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47865 p hg
    simpa only [d8118, d1253, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49127 (p : Pattern) (guard : d8124 p = 1) : d1254 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1254, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49126 p hg
    simpa only [d8124, d1254, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1254, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48919 p hg
    simpa only [d8124, d1254, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49128 (p : Pattern) (guard : d8130 p = 1) : d1255 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1255, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49127 p hg
    simpa only [d8130, d1255, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1255, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48922 p hg
    simpa only [d8130, d1255, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49129 (p : Pattern) (guard : d8131 p = 1) : d1256 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1256, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49124 p hg
    simpa only [d8131, d1256, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1256, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49128 p hg
    simpa only [d8131, d1256, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49130 (p : Pattern) (guard : d8132 p = 1) : d1257 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1257, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49120 p hg
    simpa only [d8132, d1257, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1257, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49129 p hg
    simpa only [d8132, d1257, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49131 (p : Pattern) (guard : d8113 p = 1) : d1178 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1178, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48978 p hg
    simpa only [d8113, d1178, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1178, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48990 p hg
    simpa only [d8113, d1178, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49132 (p : Pattern) (guard : d8118 p = 1) : d1179 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1179, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48929 p hg
    simpa only [d8118, d1179, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1179, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d8118, d1179, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49133 (p : Pattern) (guard : d8119 p = 1) : d1180 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1180, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49131 p hg
    simpa only [d8119, d1180, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1180, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49132 p hg
    simpa only [d8119, d1180, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49134 (p : Pattern) (guard : d8124 p = 1) : d1183 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1183, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48904 p hg
    simpa only [d8124, d1183, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1183, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1183, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49135 (p : Pattern) (guard : d8125 p = 1) : d1184 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1184, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49133 p hg
    simpa only [d8125, d1184, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1184, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49134 p hg
    simpa only [d8125, d1184, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49136 (p : Pattern) (guard : d8112 p = 1) : d1185 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1185, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35484 p hg
    simpa only [d8112, d1185, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1185, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47959 p hg
    simpa only [d8112, d1185, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49137 (p : Pattern) (guard : d8118 p = 1) : d1186 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1186, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49136 p hg
    simpa only [d8118, d1186, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1186, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48095 p hg
    simpa only [d8118, d1186, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49138 (p : Pattern) (guard : d8124 p = 1) : d1187 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1187, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49137 p hg
    simpa only [d8124, d1187, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1187, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48919 p hg
    simpa only [d8124, d1187, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49139 (p : Pattern) (guard : d8130 p = 1) : d1190 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1190, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49138 p hg
    simpa only [d8130, d1190, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1190, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48922 p hg
    simpa only [d8130, d1190, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
