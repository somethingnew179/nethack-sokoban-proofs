/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons073
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c10360 (pattern : Twelve) (guard : d1 pattern = 1) : d859 pattern ≤ (6 : Int) + d1311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10357 pattern childGuard
    simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10359 pattern childGuard
    simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10361 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (6 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10323 pattern childGuard
    simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10362 (pattern : Twelve) (guard : d1 pattern = 1) : d836 pattern ≤ (6 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10330 pattern childGuard
    simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10361 pattern childGuard
    simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10363 (pattern : Twelve) (guard : d1 pattern = 1) : d851 pattern ≤ (6 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10229 pattern childGuard
    simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10362 pattern childGuard
    simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10364 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (6 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10221 pattern childGuard
    simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10365 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (6 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10233 pattern childGuard
    simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10364 pattern childGuard
    simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10366 (pattern : Twelve) (guard : d1 pattern = 1) : d852 pattern ≤ (6 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10365 pattern childGuard
    simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10338 pattern childGuard
    simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10367 (pattern : Twelve) (guard : d1 pattern = 1) : d860 pattern ≤ (6 : Int) + d1312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10363 pattern childGuard
    simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10366 pattern childGuard
    simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10368 (pattern : Twelve) (guard : d1 pattern = 1) : d865 pattern ≤ (6 : Int) + d1317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10360 pattern childGuard
    simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10367 pattern childGuard
    simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10369 (pattern : Twelve) (guard : d1 pattern = 1) : d866 pattern ≤ (6 : Int) + d1318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10353 pattern childGuard
    simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10370 (pattern : Twelve) (guard : d1 pattern = 1) : d868 pattern ≤ (6 : Int) + d1320 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10368 pattern childGuard
    simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10369 pattern childGuard
    simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10371 (pattern : Twelve) (guard : d1 pattern = 1) : d870 pattern ≤ (6 : Int) + d1322 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10354 pattern childGuard
    simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10370 pattern childGuard
    simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10372 (pattern : Twelve) (guard : d1 pattern = 1) : d871 pattern ≤ (6 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10344 pattern childGuard
    simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10371 pattern childGuard
    simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10373 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (6 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10153 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10157 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10374 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (6 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10143 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10152 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10375 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (6 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10374 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10157 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10376 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (6 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10373 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10375 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10377 (pattern : Twelve) (guard : d1 pattern = 1) : d1284 pattern ≤ (6 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10376 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10375 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10378 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (6 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10154 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10377 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10379 (pattern : Twelve) (guard : d1 pattern = 1) : d1294 pattern ≤ (6 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10165 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10380 (pattern : Twelve) (guard : d1 pattern = 1) : d1305 pattern ≤ (6 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10378 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10379 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10381 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (6 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10310 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10175 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10382 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (6 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10160 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10381 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10383 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (6 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10373 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10382 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10384 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (6 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10375 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10385 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (6 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10383 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10384 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10386 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (6 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10318 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10385 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10387 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (6 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10165 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10236 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10388 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (6 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10387 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10167 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10389 (pattern : Twelve) (guard : d1 pattern = 1) : d1296 pattern ≤ (6 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10388 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10390 (pattern : Twelve) (guard : d1 pattern = 1) : d1306 pattern ≤ (6 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10386 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10389 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10391 (pattern : Twelve) (guard : d1 pattern = 1) : d1313 pattern ≤ (6 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10380 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10390 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10392 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (6 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10211 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10159 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10393 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (6 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10392 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10381 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10394 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (6 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10375 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10393 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10395 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (6 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10383 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10394 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10396 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (6 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10194 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10395 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10397 (pattern : Twelve) (guard : d1 pattern = 1) : d1298 pattern ≤ (6 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10387 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10398 (pattern : Twelve) (guard : d1 pattern = 1) : d1307 pattern ≤ (6 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10396 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10397 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10399 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (6 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10231 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10184 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10400 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (6 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10382 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10399 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10401 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (6 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10393 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10402 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (6 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10400 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10401 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10403 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (6 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10335 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10402 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10404 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (6 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10236 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10185 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10405 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (6 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10404 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10237 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10406 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (6 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10405 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10407 (pattern : Twelve) (guard : d1 pattern = 1) : d1308 pattern ≤ (6 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10403 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10406 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10408 (pattern : Twelve) (guard : d1 pattern = 1) : d1314 pattern ≤ (6 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10398 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10407 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10409 (pattern : Twelve) (guard : d1 pattern = 1) : d1315 pattern ≤ (6 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10390 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10410 (pattern : Twelve) (guard : d1 pattern = 1) : d1319 pattern ≤ (6 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10408 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10409 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10411 (pattern : Twelve) (guard : d1 pattern = 1) : d1321 pattern ≤ (6 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10391 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10410 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10412 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (6 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10165 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10193 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10413 (pattern : Twelve) (guard : d1 pattern = 1) : d1301 pattern ≤ (6 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10412 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10414 (pattern : Twelve) (guard : d1 pattern = 1) : d1309 pattern ≤ (6 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10378 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10413 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10415 (pattern : Twelve) (guard : d1 pattern = 1) : d1290 pattern ≤ (6 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10387 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10253 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10416 (pattern : Twelve) (guard : d1 pattern = 1) : d1302 pattern ≤ (6 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10415 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10417 (pattern : Twelve) (guard : d1 pattern = 1) : d1310 pattern ≤ (6 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10386 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10416 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10418 (pattern : Twelve) (guard : d1 pattern = 1) : d1316 pattern ≤ (6 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10414 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10417 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10419 (pattern : Twelve) (guard : d1 pattern = 1) : d1291 pattern ≤ (6 : Int) + d821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10387 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10233 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10420 (pattern : Twelve) (guard : d1 pattern = 1) : d1303 pattern ≤ (6 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10419 pattern childGuard
    simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10421 (pattern : Twelve) (guard : d1 pattern = 1) : d1311 pattern ≤ (6 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10396 pattern childGuard
    simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10420 pattern childGuard
    simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10422 (pattern : Twelve) (guard : d1 pattern = 1) : d1292 pattern ≤ (6 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10404 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10279 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10423 (pattern : Twelve) (guard : d1 pattern = 1) : d1304 pattern ≤ (6 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10422 pattern childGuard
    simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10424 (pattern : Twelve) (guard : d1 pattern = 1) : d1312 pattern ≤ (6 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10403 pattern childGuard
    simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10423 pattern childGuard
    simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10425 (pattern : Twelve) (guard : d1 pattern = 1) : d1317 pattern ≤ (6 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10421 pattern childGuard
    simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10424 pattern childGuard
    simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10426 (pattern : Twelve) (guard : d1 pattern = 1) : d1318 pattern ≤ (6 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10417 pattern childGuard
    simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10427 (pattern : Twelve) (guard : d1 pattern = 1) : d1320 pattern ≤ (6 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10425 pattern childGuard
    simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10426 pattern childGuard
    simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10428 (pattern : Twelve) (guard : d1 pattern = 1) : d1322 pattern ≤ (6 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10418 pattern childGuard
    simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10427 pattern childGuard
    simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10429 (pattern : Twelve) (guard : d1 pattern = 1) : d1323 pattern ≤ (6 : Int) + d1664 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10411 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10428 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10430 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10301 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10303 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10431 (pattern : Twelve) (guard : d1 pattern = 1) : d1649 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10302 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10430 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10432 (pattern : Twelve) (guard : d1 pattern = 1) : d1650 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10304 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10433 (pattern : Twelve) (guard : d1 pattern = 1) : d1656 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10431 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10432 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10434 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10302 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10435 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10305 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10434 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10436 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10430 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10177 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10437 (pattern : Twelve) (guard : d1 pattern = 1) : d1645 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10430 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10438 (pattern : Twelve) (guard : d1 pattern = 1) : d1647 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10436 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10437 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10439 (pattern : Twelve) (guard : d1 pattern = 1) : d1651 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10435 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10438 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10440 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10336 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10306 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10441 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10440 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10442 (pattern : Twelve) (guard : d1 pattern = 1) : d1657 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10439 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10441 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10443 (pattern : Twelve) (guard : d1 pattern = 1) : d1660 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10433 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10442 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10444 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10305 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10436 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10445 (pattern : Twelve) (guard : d1 pattern = 1) : d1653 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10336 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10446 (pattern : Twelve) (guard : d1 pattern = 1) : d1658 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10444 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10445 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10447 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10177 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10189 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10448 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10177 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10449 (pattern : Twelve) (guard : d1 pattern = 1) : d1648 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10447 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10448 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10450 (pattern : Twelve) (guard : d1 pattern = 1) : d1654 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10440 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10449 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10451 (pattern : Twelve) (guard : d1 pattern = 1) : d1655 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10337 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10452 (pattern : Twelve) (guard : d1 pattern = 1) : d1659 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10450 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10451 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10453 (pattern : Twelve) (guard : d1 pattern = 1) : d1661 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10446 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10452 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10454 (pattern : Twelve) (guard : d1 pattern = 1) : d1662 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10442 pattern childGuard
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10455 (pattern : Twelve) (guard : d1 pattern = 1) : d1663 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10453 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10454 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10456 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10443 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10455 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10457 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (4 : Int) + d72 pattern := by
  omega
theorem c10458 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (4 : Int) + d0 pattern := by
  omega
theorem c10459 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (4 : Int) + d17 pattern := by
  omega
theorem c10460 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (4 : Int) + d2 pattern := by
  change (1 : Int) ≤ (4 : Int) + 2
  decide
theorem c10461 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (4 : Int) + d2 pattern := by
  omega
theorem c10462 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (4 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10460 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10461 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10463 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (4 : Int) + d9 pattern := by
  omega
theorem c10464 (pattern : Twelve) (guard : d1 pattern = 1) : d18 pattern ≤ (4 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10462 pattern childGuard
    simpa only [d18, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10463 pattern childGuard
    simpa only [d18, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10465 (pattern : Twelve) (guard : d1 pattern = 1) : d28 pattern ≤ (4 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10459 pattern childGuard
    simpa only [d28, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10464 pattern childGuard
    simpa only [d28, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10466 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (4 : Int) + d29 pattern := by
  omega
theorem c10467 (pattern : Twelve) (guard : d1 pattern = 1) : d51 pattern ≤ (4 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10465 pattern childGuard
    simpa only [d51, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10466 pattern childGuard
    simpa only [d51, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10468 (pattern : Twelve) (guard : d1 pattern = 1) : d73 pattern ≤ (4 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10458 pattern childGuard
    simpa only [d73, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10467 pattern childGuard
    simpa only [d73, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10469 (pattern : Twelve) (guard : d1 pattern = 1) : d91 pattern ≤ (4 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10457 pattern childGuard
    simpa only [d91, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10468 pattern childGuard
    simpa only [d91, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10470 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (4 : Int) + d30 pattern := by
  omega
theorem c10471 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (4 : Int) + d6 pattern := by
  change (3 : Int) ≤ (4 : Int) + 6
  decide
theorem c10472 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (4 : Int) + d6 pattern := by
  change (5 : Int) ≤ (4 : Int) + 6
  decide
theorem c10473 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10471 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10472 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10474 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (4 : Int) + d6 pattern := by
  change (4 : Int) ≤ (4 : Int) + 6
  decide
theorem c10475 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (4 : Int) + d6 pattern := by
  omega
theorem c10476 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10474 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10477 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10473 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10476 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10478 (pattern : Twelve) (guard : d1 pattern = 1) : d31 pattern ≤ (4 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10458 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10477 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10479 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (4 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10470 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10478 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10480 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10472 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10481 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10476 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10480 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10482 (pattern : Twelve) (guard : d1 pattern = 1) : d32 pattern ≤ (4 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10459 pattern childGuard
    simpa only [d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10481 pattern childGuard
    simpa only [d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10483 (pattern : Twelve) (guard : d1 pattern = 1) : d53 pattern ≤ (4 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10470 pattern childGuard
    simpa only [d53, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10482 pattern childGuard
    simpa only [d53, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10484 (pattern : Twelve) (guard : d1 pattern = 1) : d74 pattern ≤ (4 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10479 pattern childGuard
    simpa only [d74, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10483 pattern childGuard
    simpa only [d74, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10485 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10480 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10486 (pattern : Twelve) (guard : d1 pattern = 1) : d33 pattern ≤ (4 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10458 pattern childGuard
    simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10485 pattern childGuard
    simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10487 (pattern : Twelve) (guard : d1 pattern = 1) : d54 pattern ≤ (4 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10470 pattern childGuard
    simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10486 pattern childGuard
    simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10488 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (4 : Int) + d55 pattern := by
  omega
theorem c10489 (pattern : Twelve) (guard : d1 pattern = 1) : d75 pattern ≤ (4 : Int) + d78 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10487 pattern childGuard
    simpa only [d75, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10488 pattern childGuard
    simpa only [d75, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10490 (pattern : Twelve) (guard : d1 pattern = 1) : d92 pattern ≤ (4 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10484 pattern childGuard
    simpa only [d92, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10489 pattern childGuard
    simpa only [d92, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10491 (pattern : Twelve) (guard : d1 pattern = 1) : d102 pattern ≤ (4 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10469 pattern childGuard
    simpa only [d102, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10490 pattern childGuard
    simpa only [d102, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10492 (pattern : Twelve) (guard : d0 pattern = 1) : d103 pattern ≤ (4 : Int) + d103 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10493 (pattern : Twelve) (guard : d1835 pattern = 1) : d110 pattern ≤ (4 : Int) + d103 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10491 pattern childGuard
    simpa only [d1835, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10492 pattern childGuard
    simpa only [d1835, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10494 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (4 : Int) + d6 pattern := by
  change (2 : Int) ≤ (4 : Int) + 6
  decide
theorem c10495 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (4 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10458 pattern childGuard
    simpa only [d30, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10494 pattern childGuard
    simpa only [d30, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10496 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (4 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10470 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10495 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10497 (pattern : Twelve) (guard : d1 pattern = 1) : d37 pattern ≤ (4 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10459 pattern childGuard
    simpa only [d37, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10471 pattern childGuard
    simpa only [d37, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10498 (pattern : Twelve) (guard : d1 pattern = 1) : d58 pattern ≤ (4 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10470 pattern childGuard
    simpa only [d58, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10497 pattern childGuard
    simpa only [d58, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10499 (pattern : Twelve) (guard : d1 pattern = 1) : d79 pattern ≤ (4 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10496 pattern childGuard
    simpa only [d79, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10498 pattern childGuard
    simpa only [d79, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
