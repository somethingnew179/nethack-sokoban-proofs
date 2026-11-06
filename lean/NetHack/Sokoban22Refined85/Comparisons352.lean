/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons351
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare49280 (p : Pattern) (guard : d8124 p = 1) : d1299 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1299, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49278 p hg
    simpa only [d8124, d1299, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1299, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49279 p hg
    simpa only [d8124, d1299, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49281 (p : Pattern) (guard : d8130 p = 1) : d1302 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1302, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49280 p hg
    simpa only [d8130, d1302, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1302, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49038 p hg
    simpa only [d8130, d1302, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49282 (p : Pattern) (guard : d8117 p = 1) : d1296 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1296, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35797 p hg
    simpa only [d8117, d1296, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1296, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35767 p hg
    simpa only [d8117, d1296, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49283 (p : Pattern) (guard : d8123 p = 1) : d1332 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1332, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49282 p hg
    simpa only [d8123, d1332, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1332, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10232 p hg
    simpa only [d8123, d1332, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49284 (p : Pattern) (guard : d8129 p = 1) : d1333 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1333, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49283 p hg
    simpa only [d8129, d1333, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1333, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49084 p hg
    simpa only [d8129, d1333, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49285 (p : Pattern) (guard : d8135 p = 1) : d1334 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1334, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49284 p hg
    simpa only [d8135, d1334, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1334, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49086 p hg
    simpa only [d8135, d1334, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49286 (p : Pattern) (guard : d8136 p = 1) : d1362 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1362, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49281 p hg
    simpa only [d8136, d1362, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1362, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49285 p hg
    simpa only [d8136, d1362, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49287 (p : Pattern) (guard : d8137 p = 1) : d1363 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1363, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49277 p hg
    simpa only [d8137, d1363, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1363, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49286 p hg
    simpa only [d8137, d1363, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49288 (p : Pattern) (guard : d8117 p = 1) : d1296 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1296, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35783 p hg
    simpa only [d8117, d1296, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1296, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1296, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49289 (p : Pattern) (guard : d8118 p = 1) : d1309 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1309, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49259 p hg
    simpa only [d8118, d1309, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1309, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49288 p hg
    simpa only [d8118, d1309, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49290 (p : Pattern) (guard : d8123 p = 1) : d1298 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1298, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49093 p hg
    simpa only [d8123, d1298, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1298, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d8123, d1298, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49291 (p : Pattern) (guard : d8124 p = 1) : d1310 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1310, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49289 p hg
    simpa only [d8124, d1310, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1310, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49290 p hg
    simpa only [d8124, d1310, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49292 (p : Pattern) (guard : d8129 p = 1) : d1301 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1301, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49070 p hg
    simpa only [d8129, d1301, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1301, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1301, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49293 (p : Pattern) (guard : d8130 p = 1) : d1311 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1311, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49291 p hg
    simpa only [d8130, d1311, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1311, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49292 p hg
    simpa only [d8130, d1311, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49294 (p : Pattern) (guard : d8117 p = 1) : d1296 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1296, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35820 p hg
    simpa only [d8117, d1296, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1296, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35764 p hg
    simpa only [d8117, d1296, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49295 (p : Pattern) (guard : d8123 p = 1) : d1332 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1332, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49294 p hg
    simpa only [d8123, d1332, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1332, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10244 p hg
    simpa only [d8123, d1332, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49296 (p : Pattern) (guard : d8129 p = 1) : d1333 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1333, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49295 p hg
    simpa only [d8129, d1333, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1333, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49084 p hg
    simpa only [d8129, d1333, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49297 (p : Pattern) (guard : d8135 p = 1) : d1334 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1334, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49296 p hg
    simpa only [d8135, d1334, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1334, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49086 p hg
    simpa only [d8135, d1334, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49298 (p : Pattern) (guard : d8136 p = 1) : d1364 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1364, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49293 p hg
    simpa only [d8136, d1364, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1364, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49297 p hg
    simpa only [d8136, d1364, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49299 (p : Pattern) (guard : d8142 p = 1) : d1365 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1365, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49298 p hg
    simpa only [d8142, d1365, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1365, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38307 p hg
    simpa only [d8142, d1365, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49300 (p : Pattern) (guard : d8143 p = 1) : d1366 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1366, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49287 p hg
    simpa only [d8143, d1366, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1366, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49299 p hg
    simpa only [d8143, d1366, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49301 (p : Pattern) (guard : d8112 p = 1) : d1319 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1319, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35706 p hg
    simpa only [d8112, d1319, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1319, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35805 p hg
    simpa only [d8112, d1319, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49302 (p : Pattern) (guard : d8118 p = 1) : d1367 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1367, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49301 p hg
    simpa only [d8118, d1367, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1367, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49282 p hg
    simpa only [d8118, d1367, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49303 (p : Pattern) (guard : d8123 p = 1) : d1298 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1298, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49288 p hg
    simpa only [d8123, d1298, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1298, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d8123, d1298, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49304 (p : Pattern) (guard : d8124 p = 1) : d1368 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1368, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49302 p hg
    simpa only [d8124, d1368, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1368, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49303 p hg
    simpa only [d8124, d1368, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49305 (p : Pattern) (guard : d8117 p = 1) : d1369 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1369, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35828 p hg
    simpa only [d8117, d1369, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1369, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1369, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49306 (p : Pattern) (guard : d8123 p = 1) : d1371 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1371, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49305 p hg
    simpa only [d8123, d1371, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1371, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10309 p hg
    simpa only [d8123, d1371, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49307 (p : Pattern) (guard : d0 p = 1) : d1372 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49308 (p : Pattern) (guard : d8129 p = 1) : d1373 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1373, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49306 p hg
    simpa only [d8129, d1373, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1373, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49307 p hg
    simpa only [d8129, d1373, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49309 (p : Pattern) (guard : d8130 p = 1) : d1374 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1374, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49304 p hg
    simpa only [d8130, d1374, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1374, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49308 p hg
    simpa only [d8130, d1374, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49310 (p : Pattern) (guard : d8117 p = 1) : d1296 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1296, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35838 p hg
    simpa only [d8117, d1296, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1296, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38311 p hg
    simpa only [d8117, d1296, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49311 (p : Pattern) (guard : d8123 p = 1) : d1332 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1332, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49310 p hg
    simpa only [d8123, d1332, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1332, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10259 p hg
    simpa only [d8123, d1332, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49312 (p : Pattern) (guard : d0 p = 1) : d1300 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49313 (p : Pattern) (guard : d8129 p = 1) : d1333 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1333, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49311 p hg
    simpa only [d8129, d1333, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1333, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49312 p hg
    simpa only [d8129, d1333, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49314 (p : Pattern) (guard : d0 p = 1) : d1378 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49315 (p : Pattern) (guard : d8135 p = 1) : d1379 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1379, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49313 p hg
    simpa only [d8135, d1379, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1379, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49314 p hg
    simpa only [d8135, d1379, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49316 (p : Pattern) (guard : d8136 p = 1) : d1380 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1380, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49309 p hg
    simpa only [d8136, d1380, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1380, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49315 p hg
    simpa only [d8136, d1380, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49317 (p : Pattern) (guard : d8123 p = 1) : d1381 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1381, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49288 p hg
    simpa only [d8123, d1381, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1381, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10322 p hg
    simpa only [d8123, d1381, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49318 (p : Pattern) (guard : d0 p = 1) : d1382 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49319 (p : Pattern) (guard : d8129 p = 1) : d1383 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1383, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49317 p hg
    simpa only [d8129, d1383, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1383, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49318 p hg
    simpa only [d8129, d1383, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49320 (p : Pattern) (guard : d8135 p = 1) : d1384 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1384, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49319 p hg
    simpa only [d8135, d1384, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1384, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49086 p hg
    simpa only [d8135, d1384, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49321 (p : Pattern) (guard : d0 p = 1) : d1390 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49322 (p : Pattern) (guard : d8141 p = 1) : d1391 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d1391, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49320 p hg
    simpa only [d8141, d1391, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d1391, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49321 p hg
    simpa only [d8141, d1391, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49323 (p : Pattern) (guard : d8142 p = 1) : d1392 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1392, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49316 p hg
    simpa only [d8142, d1392, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1392, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49322 p hg
    simpa only [d8142, d1392, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49324 (p : Pattern) (guard : d8123 p = 1) : d1381 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1381, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49282 p hg
    simpa only [d8123, d1381, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1381, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10322 p hg
    simpa only [d8123, d1381, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49325 (p : Pattern) (guard : d8129 p = 1) : d1383 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1383, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49324 p hg
    simpa only [d8129, d1383, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1383, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49318 p hg
    simpa only [d8129, d1383, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49326 (p : Pattern) (guard : d8135 p = 1) : d1384 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1384, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49325 p hg
    simpa only [d8135, d1384, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1384, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49086 p hg
    simpa only [d8135, d1384, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49327 (p : Pattern) (guard : d0 p = 1) : d1390 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49328 (p : Pattern) (guard : d8141 p = 1) : d1391 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d1391, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49326 p hg
    simpa only [d8141, d1391, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d1391, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49327 p hg
    simpa only [d8141, d1391, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49329 (p : Pattern) (guard : d8147 p = 1) : d1393 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d1393, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49328 p hg
    simpa only [d8147, d1393, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d1393, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d1393, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49330 (p : Pattern) (guard : d8148 p = 1) : d1394 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d1394, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49323 p hg
    simpa only [d8148, d1394, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d1394, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49329 p hg
    simpa only [d8148, d1394, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49331 (p : Pattern) (guard : d8149 p = 1) : d1395 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d1395, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49300 p hg
    simpa only [d8149, d1395, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d1395, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49330 p hg
    simpa only [d8149, d1395, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49332 (p : Pattern) (guard : d8150 p = 1) : d1396 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d1396, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49256 p hg
    simpa only [d8150, d1396, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d1396, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49331 p hg
    simpa only [d8150, d1396, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49333 (p : Pattern) (guard : d8151 p = 1) : d1397 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49190 p hg
    simpa only [d8151, d1397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49332 p hg
    simpa only [d8151, d1397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49334 (p : Pattern) (guard : d8152 p = 1) : d1398 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49102 p hg
    simpa only [d8152, d1398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49333 p hg
    simpa only [d8152, d1398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49335 (p : Pattern) (guard : d0 p = 1) : d304 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49336 (p : Pattern) (guard : d8141 p = 1) : d305 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d305, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38326 p hg
    simpa only [d8141, d305, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d305, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49335 p hg
    simpa only [d8141, d305, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49337 (p : Pattern) (guard : d8147 p = 1) : d307 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d307, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49336 p hg
    simpa only [d8147, d307, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d307, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d307, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49338 (p : Pattern) (guard : d8148 p = 1) : d308 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d308, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35853 p hg
    simpa only [d8148, d308, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d308, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49337 p hg
    simpa only [d8148, d308, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49339 (p : Pattern) (guard : d8149 p = 1) : d309 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d309, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41513 p hg
    simpa only [d8149, d309, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d309, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49338 p hg
    simpa only [d8149, d309, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49340 (p : Pattern) (guard : d8150 p = 1) : d310 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d310, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41505 p hg
    simpa only [d8150, d310, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d310, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49339 p hg
    simpa only [d8150, d310, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49341 (p : Pattern) (guard : d8151 p = 1) : d311 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48311 p hg
    simpa only [d8151, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49340 p hg
    simpa only [d8151, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49342 (p : Pattern) (guard : d8152 p = 1) : d312 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41443 p hg
    simpa only [d8152, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49341 p hg
    simpa only [d8152, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49343 (p : Pattern) (guard : d8097 p = 1) : d346 p ≤ (0 : Int) + d346 p := by
  omega
theorem compare49344 (p : Pattern) (guard : d8098 p = 1) : d949 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8093 p = 1 := by simpa only [d8098, d949, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34347 p hg
    simpa only [d8098, d949, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8097 p = 1 := by simpa only [d8098, d949, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49343 p hg
    simpa only [d8098, d949, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49345 (p : Pattern) (guard : d8102 p = 1) : d361 p ≤ (0 : Int) + d361 p := by
  omega
theorem compare49346 (p : Pattern) (guard : d8103 p = 1) : d951 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d951, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47678 p hg
    simpa only [d8103, d951, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d951, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49345 p hg
    simpa only [d8103, d951, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49347 (p : Pattern) (guard : d8104 p = 1) : d952 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8098 p = 1 := by simpa only [d8104, d952, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49344 p hg
    simpa only [d8104, d952, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8103 p = 1 := by simpa only [d8104, d952, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49346 p hg
    simpa only [d8104, d952, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49348 (p : Pattern) (guard : d8102 p = 1) : d371 p ≤ (0 : Int) + d371 p := by
  omega
theorem compare49349 (p : Pattern) (guard : d8103 p = 1) : d953 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d953, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47681 p hg
    simpa only [d8103, d953, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d953, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49348 p hg
    simpa only [d8103, d953, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49350 (p : Pattern) (guard : d8107 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare49351 (p : Pattern) (guard : d8108 p = 1) : d954 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d954, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34450 p hg
    simpa only [d8108, d954, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d954, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49350 p hg
    simpa only [d8108, d954, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49352 (p : Pattern) (guard : d8109 p = 1) : d955 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d955, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49349 p hg
    simpa only [d8109, d955, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d955, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49351 p hg
    simpa only [d8109, d955, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49353 (p : Pattern) (guard : d8110 p = 1) : d956 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8104 p = 1 := by simpa only [d8110, d956, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49347 p hg
    simpa only [d8110, d956, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8109 p = 1 := by simpa only [d8110, d956, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49352 p hg
    simpa only [d8110, d956, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49354 (p : Pattern) (guard : d8102 p = 1) : d369 p ≤ (0 : Int) + d369 p := by
  omega
theorem compare49355 (p : Pattern) (guard : d8103 p = 1) : d957 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d957, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34478 p hg
    simpa only [d8103, d957, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d957, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49354 p hg
    simpa only [d8103, d957, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49356 (p : Pattern) (guard : d8107 p = 1) : d374 p ≤ (0 : Int) + d374 p := by
  omega
theorem compare49357 (p : Pattern) (guard : d8108 p = 1) : d958 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d958, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47699 p hg
    simpa only [d8108, d958, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d958, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49356 p hg
    simpa only [d8108, d958, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49358 (p : Pattern) (guard : d8109 p = 1) : d959 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d959, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49355 p hg
    simpa only [d8109, d959, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d959, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49357 p hg
    simpa only [d8109, d959, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49359 (p : Pattern) (guard : d8108 p = 1) : d960 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d960, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47707 p hg
    simpa only [d8108, d960, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d960, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49350 p hg
    simpa only [d8108, d960, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49360 (p : Pattern) (guard : d8113 p = 1) : d961 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43664 p hg
    simpa only [d8113, d961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49361 (p : Pattern) (guard : d8114 p = 1) : d962 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d962, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49359 p hg
    simpa only [d8114, d962, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d962, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49360 p hg
    simpa only [d8114, d962, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49362 (p : Pattern) (guard : d8115 p = 1) : d963 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d963, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49358 p hg
    simpa only [d8115, d963, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d963, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49361 p hg
    simpa only [d8115, d963, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49363 (p : Pattern) (guard : d8116 p = 1) : d964 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8110 p = 1 := by simpa only [d8116, d964, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49353 p hg
    simpa only [d8116, d964, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8115 p = 1 := by simpa only [d8116, d964, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49362 p hg
    simpa only [d8116, d964, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49364 (p : Pattern) (guard : d8103 p = 1) : d965 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d965, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34551 p hg
    simpa only [d8103, d965, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d965, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49345 p hg
    simpa only [d8103, d965, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49365 (p : Pattern) (guard : d8108 p = 1) : d966 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d966, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47713 p hg
    simpa only [d8108, d966, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d966, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49350 p hg
    simpa only [d8108, d966, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49366 (p : Pattern) (guard : d8109 p = 1) : d967 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d967, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49364 p hg
    simpa only [d8109, d967, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d967, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49365 p hg
    simpa only [d8109, d967, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49367 (p : Pattern) (guard : d8108 p = 1) : d968 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d968, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47716 p hg
    simpa only [d8108, d968, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d968, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49350 p hg
    simpa only [d8108, d968, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49368 (p : Pattern) (guard : d8114 p = 1) : d969 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d969, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49367 p hg
    simpa only [d8114, d969, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d969, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d969, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49369 (p : Pattern) (guard : d8115 p = 1) : d970 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d970, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49366 p hg
    simpa only [d8115, d970, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d970, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49368 p hg
    simpa only [d8115, d970, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49370 (p : Pattern) (guard : d8108 p = 1) : d971 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d971, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34591 p hg
    simpa only [d8108, d971, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d971, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49356 p hg
    simpa only [d8108, d971, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49371 (p : Pattern) (guard : d8114 p = 1) : d973 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d973, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49370 p hg
    simpa only [d8114, d973, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d973, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47725 p hg
    simpa only [d8114, d973, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49372 (p : Pattern) (guard : d8120 p = 1) : d975 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d975, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49371 p hg
    simpa only [d8120, d975, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d975, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47726 p hg
    simpa only [d8120, d975, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49373 (p : Pattern) (guard : d8121 p = 1) : d976 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d976, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49369 p hg
    simpa only [d8121, d976, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d976, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49372 p hg
    simpa only [d8121, d976, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49374 (p : Pattern) (guard : d8122 p = 1) : d977 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8116 p = 1 := by simpa only [d8122, d977, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49363 p hg
    simpa only [d8122, d977, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8121 p = 1 := by simpa only [d8122, d977, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49373 p hg
    simpa only [d8122, d977, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49375 (p : Pattern) (guard : d8102 p = 1) : d389 p ≤ (0 : Int) + d389 p := by
  omega
theorem compare49376 (p : Pattern) (guard : d8103 p = 1) : d978 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d978, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38103 p hg
    simpa only [d8103, d978, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d978, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49375 p hg
    simpa only [d8103, d978, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49377 (p : Pattern) (guard : d8108 p = 1) : d966 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d966, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47730 p hg
    simpa only [d8108, d966, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d966, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49350 p hg
    simpa only [d8108, d966, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49378 (p : Pattern) (guard : d8109 p = 1) : d979 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d979, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49376 p hg
    simpa only [d8109, d979, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d979, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49377 p hg
    simpa only [d8109, d979, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49379 (p : Pattern) (guard : d8108 p = 1) : d968 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d968, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47733 p hg
    simpa only [d8108, d968, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d968, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49350 p hg
    simpa only [d8108, d968, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49380 (p : Pattern) (guard : d8114 p = 1) : d969 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d969, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49379 p hg
    simpa only [d8114, d969, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d969, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d969, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49381 (p : Pattern) (guard : d8115 p = 1) : d980 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d980, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49378 p hg
    simpa only [d8115, d980, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d980, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49380 p hg
    simpa only [d8115, d980, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49382 (p : Pattern) (guard : d8107 p = 1) : d371 p ≤ (0 : Int) + d371 p := by
  omega
theorem compare49383 (p : Pattern) (guard : d8108 p = 1) : d981 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d981, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41378 p hg
    simpa only [d8108, d981, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d981, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49382 p hg
    simpa only [d8108, d981, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49384 (p : Pattern) (guard : d8113 p = 1) : d972 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d972, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47739 p hg
    simpa only [d8113, d972, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d972, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d972, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49385 (p : Pattern) (guard : d8114 p = 1) : d982 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d982, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49383 p hg
    simpa only [d8114, d982, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d982, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49384 p hg
    simpa only [d8114, d982, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49386 (p : Pattern) (guard : d8120 p = 1) : d983 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d983, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49385 p hg
    simpa only [d8120, d983, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d983, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47726 p hg
    simpa only [d8120, d983, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49387 (p : Pattern) (guard : d8121 p = 1) : d984 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d984, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49381 p hg
    simpa only [d8121, d984, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d984, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49386 p hg
    simpa only [d8121, d984, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49388 (p : Pattern) (guard : d8108 p = 1) : d985 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d985, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38117 p hg
    simpa only [d8108, d985, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d985, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49350 p hg
    simpa only [d8108, d985, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49389 (p : Pattern) (guard : d8114 p = 1) : d986 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d986, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49388 p hg
    simpa only [d8114, d986, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d986, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38119 p hg
    simpa only [d8114, d986, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49390 (p : Pattern) (guard : d8120 p = 1) : d987 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d987, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49389 p hg
    simpa only [d8120, d987, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d987, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38121 p hg
    simpa only [d8120, d987, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49391 (p : Pattern) (guard : d8126 p = 1) : d988 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d988, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49390 p hg
    simpa only [d8126, d988, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d988, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41388 p hg
    simpa only [d8126, d988, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49392 (p : Pattern) (guard : d8127 p = 1) : d989 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d989, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49387 p hg
    simpa only [d8127, d989, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d989, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49391 p hg
    simpa only [d8127, d989, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49393 (p : Pattern) (guard : d8128 p = 1) : d990 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d990, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49374 p hg
    simpa only [d8128, d990, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d990, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49392 p hg
    simpa only [d8128, d990, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49394 (p : Pattern) (guard : d8102 p = 1) : d386 p ≤ (0 : Int) + d386 p := by
  omega
theorem compare49395 (p : Pattern) (guard : d8103 p = 1) : d991 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d991, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34623 p hg
    simpa only [d8103, d991, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d991, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49394 p hg
    simpa only [d8103, d991, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49396 (p : Pattern) (guard : d8108 p = 1) : d992 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d992, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47747 p hg
    simpa only [d8108, d992, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d992, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49350 p hg
    simpa only [d8108, d992, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49397 (p : Pattern) (guard : d8109 p = 1) : d993 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d993, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49395 p hg
    simpa only [d8109, d993, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d993, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49396 p hg
    simpa only [d8109, d993, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49398 (p : Pattern) (guard : d8108 p = 1) : d994 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d994, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47751 p hg
    simpa only [d8108, d994, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d994, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49350 p hg
    simpa only [d8108, d994, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49399 (p : Pattern) (guard : d8113 p = 1) : d954 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34648 p hg
    simpa only [d8113, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49400 (p : Pattern) (guard : d8114 p = 1) : d995 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d995, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49398 p hg
    simpa only [d8114, d995, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d995, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49399 p hg
    simpa only [d8114, d995, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49401 (p : Pattern) (guard : d8115 p = 1) : d996 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d996, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49397 p hg
    simpa only [d8115, d996, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d996, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49400 p hg
    simpa only [d8115, d996, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49402 (p : Pattern) (guard : d8107 p = 1) : d361 p ≤ (0 : Int) + d361 p := by
  omega
theorem compare49403 (p : Pattern) (guard : d8108 p = 1) : d997 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d997, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34662 p hg
    simpa only [d8108, d997, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d997, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49402 p hg
    simpa only [d8108, d997, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49404 (p : Pattern) (guard : d8113 p = 1) : d960 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d960, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47758 p hg
    simpa only [d8113, d960, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d960, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d960, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49405 (p : Pattern) (guard : d8114 p = 1) : d998 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d998, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49403 p hg
    simpa only [d8114, d998, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d998, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49404 p hg
    simpa only [d8114, d998, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49406 (p : Pattern) (guard : d8113 p = 1) : d960 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d960, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47761 p hg
    simpa only [d8113, d960, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d960, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d960, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49407 (p : Pattern) (guard : d8118 p = 1) : d961 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43786 p hg
    simpa only [d8118, d961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49408 (p : Pattern) (guard : d8119 p = 1) : d962 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d962, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49406 p hg
    simpa only [d8119, d962, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d962, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49407 p hg
    simpa only [d8119, d962, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49409 (p : Pattern) (guard : d8120 p = 1) : d999 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d999, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49405 p hg
    simpa only [d8120, d999, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d999, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49408 p hg
    simpa only [d8120, d999, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49410 (p : Pattern) (guard : d8121 p = 1) : d1000 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1000, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49401 p hg
    simpa only [d8121, d1000, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1000, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49409 p hg
    simpa only [d8121, d1000, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49411 (p : Pattern) (guard : d8108 p = 1) : d1001 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1001, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34698 p hg
    simpa only [d8108, d1001, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1001, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49350 p hg
    simpa only [d8108, d1001, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49412 (p : Pattern) (guard : d8113 p = 1) : d966 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47767 p hg
    simpa only [d8113, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49413 (p : Pattern) (guard : d8114 p = 1) : d1002 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1002, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49411 p hg
    simpa only [d8114, d1002, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1002, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49412 p hg
    simpa only [d8114, d1002, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49414 (p : Pattern) (guard : d8113 p = 1) : d968 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47770 p hg
    simpa only [d8113, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49415 (p : Pattern) (guard : d8119 p = 1) : d969 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49414 p hg
    simpa only [d8119, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49416 (p : Pattern) (guard : d8120 p = 1) : d1003 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1003, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49413 p hg
    simpa only [d8120, d1003, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1003, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49415 p hg
    simpa only [d8120, d1003, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49417 (p : Pattern) (guard : d8113 p = 1) : d966 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d966, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34723 p hg
    simpa only [d8113, d966, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d966, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d966, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49418 (p : Pattern) (guard : d8119 p = 1) : d1004 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1004, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49417 p hg
    simpa only [d8119, d1004, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1004, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47779 p hg
    simpa only [d8119, d1004, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49419 (p : Pattern) (guard : d8125 p = 1) : d1005 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1005, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49418 p hg
    simpa only [d8125, d1005, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1005, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47780 p hg
    simpa only [d8125, d1005, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
