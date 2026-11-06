/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1400 (p : Pattern) (guard : d835 p = 1) : d198 p ≤ (1 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d835, d198, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1398 p hg
    simpa only [d835, d198, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d198, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1399 p hg
    simpa only [d835, d198, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1401 (p : Pattern) (guard : d1 p = 1) : d76 p ≤ (1 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d76, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3 p hg
    simpa only [d76, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d76, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare638 p hg
    simpa only [d76, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1402 (p : Pattern) (guard : d1 p = 1) : d77 p ≤ (1 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d77, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2 p hg
    simpa only [d77, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d77, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1401 p hg
    simpa only [d77, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1403 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare398 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1404 (p : Pattern) (guard : d1 p = 1) : d199 p ≤ (1 : Int) + d68 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14 p hg
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1403 p hg
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1405 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare393 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1406 (p : Pattern) (guard : d1 p = 1) : d200 p ≤ (1 : Int) + d70 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1405 p hg
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1407 (p : Pattern) (guard : d1 p = 1) : d201 p ≤ (1 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d201, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1404 p hg
    simpa only [d201, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d201, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1406 p hg
    simpa only [d201, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1408 (p : Pattern) (guard : d1 p = 1) : d202 p ≤ (1 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d202, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1380 p hg
    simpa only [d202, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d202, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1407 p hg
    simpa only [d202, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1409 (p : Pattern) (guard : d1 p = 1) : d203 p ≤ (1 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d203, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1381 p hg
    simpa only [d203, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d203, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1408 p hg
    simpa only [d203, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1410 (p : Pattern) (guard : d1 p = 1) : d204 p ≤ (1 : Int) + d78 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d204, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1402 p hg
    simpa only [d204, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d204, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1409 p hg
    simpa only [d204, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1411 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (1 : Int) + d83 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1412 (p : Pattern) (guard : d835 p = 1) : d205 p ≤ (1 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d835, d205, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1410 p hg
    simpa only [d835, d205, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d205, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d835, d205, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1413 (p : Pattern) (guard : d835 p = 1) : d206 p ≤ (1 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d835 p = 1 := by simpa only [d206, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1400 p hg
    simpa only [d206, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d206, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1412 p hg
    simpa only [d206, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1414 (p : Pattern) (guard : d836 p = 1) : d207 p ≤ (1 : Int) + d85 p := by
  cases selected : p 86 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d836, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1364 p hg
    simpa only [d836, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d836, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1413 p hg
    simpa only [d836, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1415 (p : Pattern) (guard : d0 p = 1) : d210 p ≤ (1 : Int) + d118 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1416 (p : Pattern) (guard : d1 p = 1) : d211 p ≤ (1 : Int) + d35 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d211, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare628 p hg
    simpa only [d211, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d211, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1387 p hg
    simpa only [d211, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1417 (p : Pattern) (guard : d1 p = 1) : d212 p ≤ (1 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d212, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1373 p hg
    simpa only [d212, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d212, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1416 p hg
    simpa only [d212, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1418 (p : Pattern) (guard : d1 p = 1) : d213 p ≤ (1 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d213, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1417 p hg
    simpa only [d213, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d213, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1395 p hg
    simpa only [d213, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1419 (p : Pattern) (guard : d1 p = 1) : d214 p ≤ (1 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d214, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1381 p hg
    simpa only [d214, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d214, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1418 p hg
    simpa only [d214, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1420 (p : Pattern) (guard : d1 p = 1) : d215 p ≤ (1 : Int) + d45 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32 p hg
    simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1419 p hg
    simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1421 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (1 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1422 (p : Pattern) (guard : d835 p = 1) : d216 p ≤ (1 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d835, d216, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1420 p hg
    simpa only [d835, d216, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d216, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1421 p hg
    simpa only [d835, d216, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1423 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (1 : Int) + d8 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1371 p hg
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1424 (p : Pattern) (guard : d1 p = 1) : d217 p ≤ (1 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d217, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1423 p hg
    simpa only [d217, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d217, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1372 p hg
    simpa only [d217, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1425 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (1 : Int) + d20 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare75 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1377 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1426 (p : Pattern) (guard : d1 p = 1) : d218 p ≤ (1 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d218, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1425 p hg
    simpa only [d218, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d218, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1378 p hg
    simpa only [d218, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1427 (p : Pattern) (guard : d1 p = 1) : d219 p ≤ (1 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d219, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1424 p hg
    simpa only [d219, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d219, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1426 p hg
    simpa only [d219, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1428 (p : Pattern) (guard : d1 p = 1) : d220 p ≤ (1 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d220, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1424 p hg
    simpa only [d220, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d220, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1427 p hg
    simpa only [d220, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1429 (p : Pattern) (guard : d1 p = 1) : d221 p ≤ (1 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d221, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1427 p hg
    simpa only [d221, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d221, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1407 p hg
    simpa only [d221, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1430 (p : Pattern) (guard : d1 p = 1) : d222 p ≤ (1 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d222, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1428 p hg
    simpa only [d222, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d222, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1429 p hg
    simpa only [d222, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1431 (p : Pattern) (guard : d1 p = 1) : d223 p ≤ (1 : Int) + d77 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1430 p hg
    simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1432 (p : Pattern) (guard : d0 p = 1) : d169 p ≤ (1 : Int) + d83 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1433 (p : Pattern) (guard : d835 p = 1) : d224 p ≤ (1 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d835, d224, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1431 p hg
    simpa only [d835, d224, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d224, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1432 p hg
    simpa only [d835, d224, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1434 (p : Pattern) (guard : d835 p = 1) : d225 p ≤ (1 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d835 p = 1 := by simpa only [d225, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1422 p hg
    simpa only [d225, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d225, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1433 p hg
    simpa only [d225, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1435 (p : Pattern) (guard : d836 p = 1) : d226 p ≤ (1 : Int) + d118 p := by
  cases selected : p 86 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d836, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1415 p hg
    simpa only [d836, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d836, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d836, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1436 (p : Pattern) (guard : d836 p = 1) : d227 p ≤ (1 : Int) + d1071 p := by
  cases selected : p 80 with
  | false =>
    have hg : d836 p = 1 := by simpa only [d227, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1414 p hg
    simpa only [d227, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d836 p = 1 := by simpa only [d227, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1435 p hg
    simpa only [d227, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1437 (p : Pattern) (guard : d857 p = 1) : d16 p ≤ (0 : Int) + d389 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d16, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d857, d16, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d16, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare853 p hg
    simpa only [d857, d16, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1438 (p : Pattern) (guard : d857 p = 1) : d26 p ≤ (0 : Int) + d390 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d26, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d857, d26, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d26, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d857, d26, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1439 (p : Pattern) (guard : d857 p = 1) : d27 p ≤ (0 : Int) + d391 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d27, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1437 p hg
    simpa only [d27, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d27, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1438 p hg
    simpa only [d27, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1440 (p : Pattern) (guard : d857 p = 1) : d28 p ≤ (0 : Int) + d392 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d28, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1437 p hg
    simpa only [d28, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d28, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1439 p hg
    simpa only [d28, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1441 (p : Pattern) (guard : d857 p = 1) : d35 p ≤ (0 : Int) + d393 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d35, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d857, d35, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d35, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare858 p hg
    simpa only [d857, d35, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1442 (p : Pattern) (guard : d857 p = 1) : d36 p ≤ (0 : Int) + d394 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d36, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1437 p hg
    simpa only [d36, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d36, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1441 p hg
    simpa only [d36, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1443 (p : Pattern) (guard : d0 p = 1) : d41 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1444 (p : Pattern) (guard : d857 p = 1) : d42 p ≤ (0 : Int) + d395 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d42, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d857, d42, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d42, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1443 p hg
    simpa only [d857, d42, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1445 (p : Pattern) (guard : d857 p = 1) : d43 p ≤ (0 : Int) + d396 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d43, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1444 p hg
    simpa only [d43, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d43, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1438 p hg
    simpa only [d43, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1446 (p : Pattern) (guard : d857 p = 1) : d44 p ≤ (0 : Int) + d397 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d44, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1442 p hg
    simpa only [d44, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d44, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1445 p hg
    simpa only [d44, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1447 (p : Pattern) (guard : d857 p = 1) : d45 p ≤ (0 : Int) + d398 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d45, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1440 p hg
    simpa only [d45, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d45, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1446 p hg
    simpa only [d45, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1448 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d408 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1449 (p : Pattern) (guard : d1072 p = 1) : d184 p ≤ (0 : Int) + d409 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d184, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1447 p hg
    simpa only [d1072, d184, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d184, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1448 p hg
    simpa only [d1072, d184, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1450 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (0 : Int) + d40 p := by
  omega
theorem compare1451 (p : Pattern) (guard : d0 p = 1) : d68 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1452 (p : Pattern) (guard : d857 p = 1) : d69 p ≤ (0 : Int) + d410 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d69, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1450 p hg
    simpa only [d857, d69, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d69, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1451 p hg
    simpa only [d857, d69, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1453 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (0 : Int) + d24 p := by
  omega
theorem compare1454 (p : Pattern) (guard : d857 p = 1) : d71 p ≤ (0 : Int) + d411 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d71, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1453 p hg
    simpa only [d857, d71, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d71, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d857, d71, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1455 (p : Pattern) (guard : d857 p = 1) : d72 p ≤ (0 : Int) + d412 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d72, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1452 p hg
    simpa only [d72, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d72, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1454 p hg
    simpa only [d72, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1456 (p : Pattern) (guard : d857 p = 1) : d73 p ≤ (0 : Int) + d413 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d73, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1439 p hg
    simpa only [d73, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d73, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1455 p hg
    simpa only [d73, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1457 (p : Pattern) (guard : d857 p = 1) : d74 p ≤ (0 : Int) + d414 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d74, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1440 p hg
    simpa only [d74, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d74, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1456 p hg
    simpa only [d74, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1458 (p : Pattern) (guard : d857 p = 1) : d68 p ≤ (0 : Int) + d199 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare881 p hg
    simpa only [d857, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1451 p hg
    simpa only [d857, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1459 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (0 : Int) + d70 p := by
  omega
theorem compare1460 (p : Pattern) (guard : d857 p = 1) : d70 p ≤ (0 : Int) + d200 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1459 p hg
    simpa only [d857, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d857, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1461 (p : Pattern) (guard : d857 p = 1) : d75 p ≤ (0 : Int) + d201 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d75, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1458 p hg
    simpa only [d75, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d75, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1460 p hg
    simpa only [d75, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1462 (p : Pattern) (guard : d857 p = 1) : d76 p ≤ (0 : Int) + d415 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d76, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1439 p hg
    simpa only [d76, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d76, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1461 p hg
    simpa only [d76, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1463 (p : Pattern) (guard : d857 p = 1) : d77 p ≤ (0 : Int) + d416 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d77, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1440 p hg
    simpa only [d77, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d77, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1462 p hg
    simpa only [d77, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1464 (p : Pattern) (guard : d857 p = 1) : d78 p ≤ (0 : Int) + d417 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d78, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1457 p hg
    simpa only [d78, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d78, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1463 p hg
    simpa only [d78, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1465 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d419 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1466 (p : Pattern) (guard : d1072 p = 1) : d185 p ≤ (0 : Int) + d420 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d185, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1464 p hg
    simpa only [d1072, d185, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d185, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1465 p hg
    simpa only [d1072, d185, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1467 (p : Pattern) (guard : d1072 p = 1) : d186 p ≤ (0 : Int) + d421 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d186, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1449 p hg
    simpa only [d186, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d186, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1466 p hg
    simpa only [d186, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1468 (p : Pattern) (guard : d857 p = 1) : d187 p ≤ (0 : Int) + d389 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d187, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d857, d187, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d187, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d857, d187, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1469 (p : Pattern) (guard : d857 p = 1) : d188 p ≤ (0 : Int) + d390 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d188, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d857, d188, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d188, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d857, d188, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1470 (p : Pattern) (guard : d857 p = 1) : d189 p ≤ (0 : Int) + d391 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d189, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1468 p hg
    simpa only [d189, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d189, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1469 p hg
    simpa only [d189, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1471 (p : Pattern) (guard : d857 p = 1) : d190 p ≤ (0 : Int) + d392 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d190, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1468 p hg
    simpa only [d190, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d190, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1470 p hg
    simpa only [d190, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1472 (p : Pattern) (guard : d857 p = 1) : d191 p ≤ (0 : Int) + d393 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d191, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d857, d191, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d191, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d857, d191, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1473 (p : Pattern) (guard : d857 p = 1) : d192 p ≤ (0 : Int) + d394 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d192, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1468 p hg
    simpa only [d192, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d192, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1472 p hg
    simpa only [d192, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1474 (p : Pattern) (guard : d857 p = 1) : d193 p ≤ (0 : Int) + d395 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d193, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d857, d193, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d193, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1451 p hg
    simpa only [d857, d193, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1475 (p : Pattern) (guard : d857 p = 1) : d194 p ≤ (0 : Int) + d396 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d194, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1474 p hg
    simpa only [d194, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d194, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1469 p hg
    simpa only [d194, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1476 (p : Pattern) (guard : d857 p = 1) : d195 p ≤ (0 : Int) + d397 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d195, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1473 p hg
    simpa only [d195, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d195, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1475 p hg
    simpa only [d195, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1477 (p : Pattern) (guard : d857 p = 1) : d196 p ≤ (0 : Int) + d398 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d196, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1471 p hg
    simpa only [d196, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d196, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1476 p hg
    simpa only [d196, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1478 (p : Pattern) (guard : d857 p = 1) : d197 p ≤ (0 : Int) + d398 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1447 p hg
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1477 p hg
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1479 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d426 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1480 (p : Pattern) (guard : d1072 p = 1) : d198 p ≤ (0 : Int) + d427 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d198, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1478 p hg
    simpa only [d1072, d198, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d198, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1479 p hg
    simpa only [d1072, d198, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1481 (p : Pattern) (guard : d857 p = 1) : d201 p ≤ (0 : Int) + d201 p := by
  omega
theorem compare1482 (p : Pattern) (guard : d857 p = 1) : d202 p ≤ (0 : Int) + d415 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d202, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1470 p hg
    simpa only [d202, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d202, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1481 p hg
    simpa only [d202, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1483 (p : Pattern) (guard : d857 p = 1) : d203 p ≤ (0 : Int) + d416 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d203, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1471 p hg
    simpa only [d203, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d203, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1482 p hg
    simpa only [d203, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1484 (p : Pattern) (guard : d857 p = 1) : d204 p ≤ (0 : Int) + d416 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1463 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1483 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1485 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (0 : Int) + d435 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1486 (p : Pattern) (guard : d1072 p = 1) : d205 p ≤ (0 : Int) + d436 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d205, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1484 p hg
    simpa only [d1072, d205, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d205, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1485 p hg
    simpa only [d1072, d205, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1487 (p : Pattern) (guard : d1072 p = 1) : d206 p ≤ (0 : Int) + d437 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d206, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1480 p hg
    simpa only [d206, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d206, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1486 p hg
    simpa only [d206, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1488 (p : Pattern) (guard : d1072 p = 1) : d207 p ≤ (0 : Int) + d438 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d207, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1467 p hg
    simpa only [d207, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d207, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1487 p hg
    simpa only [d207, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1489 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d408 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1490 (p : Pattern) (guard : d1072 p = 1) : d208 p ≤ (0 : Int) + d409 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d208, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1447 p hg
    simpa only [d1072, d208, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d208, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1489 p hg
    simpa only [d1072, d208, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1491 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (0 : Int) + d419 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1492 (p : Pattern) (guard : d1072 p = 1) : d209 p ≤ (0 : Int) + d439 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d209, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1463 p hg
    simpa only [d1072, d209, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d209, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1491 p hg
    simpa only [d1072, d209, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1493 (p : Pattern) (guard : d1072 p = 1) : d210 p ≤ (0 : Int) + d440 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d210, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1490 p hg
    simpa only [d210, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d210, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1492 p hg
    simpa only [d210, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1494 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (0 : Int) + d119 p := by
  omega
theorem compare1495 (p : Pattern) (guard : d857 p = 1) : d211 p ≤ (0 : Int) + d441 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d211, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1494 p hg
    simpa only [d857, d211, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d211, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d857, d211, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1496 (p : Pattern) (guard : d857 p = 1) : d212 p ≤ (0 : Int) + d442 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d212, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1468 p hg
    simpa only [d212, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d212, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1495 p hg
    simpa only [d212, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1497 (p : Pattern) (guard : d857 p = 1) : d213 p ≤ (0 : Int) + d443 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d213, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1496 p hg
    simpa only [d213, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d213, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1475 p hg
    simpa only [d213, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1498 (p : Pattern) (guard : d857 p = 1) : d214 p ≤ (0 : Int) + d444 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d214, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1471 p hg
    simpa only [d214, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d214, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1497 p hg
    simpa only [d214, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1499 (p : Pattern) (guard : d857 p = 1) : d215 p ≤ (0 : Int) + d445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d215, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1447 p hg
    simpa only [d215, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d215, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d215, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1500 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (0 : Int) + d448 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1501 (p : Pattern) (guard : d1072 p = 1) : d216 p ≤ (0 : Int) + d449 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d216, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d1072, d216, d449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d216, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d1072, d216, d449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1502 (p : Pattern) (guard : d857 p = 1) : d217 p ≤ (0 : Int) + d399 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d217, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d857, d217, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d217, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d857, d217, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1503 (p : Pattern) (guard : d857 p = 1) : d218 p ≤ (0 : Int) + d400 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d218, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare217 p hg
    simpa only [d857, d218, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d218, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d857, d218, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1504 (p : Pattern) (guard : d857 p = 1) : d219 p ≤ (0 : Int) + d401 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d219, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1502 p hg
    simpa only [d219, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d219, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1503 p hg
    simpa only [d219, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1505 (p : Pattern) (guard : d857 p = 1) : d220 p ≤ (0 : Int) + d402 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d220, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1502 p hg
    simpa only [d220, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d220, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1504 p hg
    simpa only [d220, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1506 (p : Pattern) (guard : d857 p = 1) : d221 p ≤ (0 : Int) + d418 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d221, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1504 p hg
    simpa only [d221, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d221, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1481 p hg
    simpa only [d221, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1507 (p : Pattern) (guard : d857 p = 1) : d222 p ≤ (0 : Int) + d419 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d222, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1505 p hg
    simpa only [d222, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d222, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d222, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1508 (p : Pattern) (guard : d857 p = 1) : d223 p ≤ (0 : Int) + d450 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d223, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1463 p hg
    simpa only [d223, d450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d223, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d223, d450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1509 (p : Pattern) (guard : d0 p = 1) : d169 p ≤ (0 : Int) + d451 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1510 (p : Pattern) (guard : d1072 p = 1) : d224 p ≤ (0 : Int) + d452 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d224, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d1072, d224, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d224, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1509 p hg
    simpa only [d1072, d224, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1511 (p : Pattern) (guard : d1072 p = 1) : d225 p ≤ (0 : Int) + d453 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d225, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1501 p hg
    simpa only [d225, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d225, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1510 p hg
    simpa only [d225, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1512 (p : Pattern) (guard : d1072 p = 1) : d226 p ≤ (0 : Int) + d454 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d226, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1493 p hg
    simpa only [d226, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d226, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1511 p hg
    simpa only [d226, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1513 (p : Pattern) (guard : d1072 p = 1) : d227 p ≤ (0 : Int) + d455 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d227, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1488 p hg
    simpa only [d227, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d227, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1512 p hg
    simpa only [d227, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1514 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d229 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1515 (p : Pattern) (guard : d868 p = 1) : d184 p ≤ (0 : Int) + d230 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d184, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare471 p hg
    simpa only [d868, d184, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d184, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1514 p hg
    simpa only [d868, d184, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1516 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d232 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1517 (p : Pattern) (guard : d868 p = 1) : d185 p ≤ (0 : Int) + d233 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d185, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare476 p hg
    simpa only [d868, d185, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d185, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1516 p hg
    simpa only [d868, d185, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1518 (p : Pattern) (guard : d868 p = 1) : d186 p ≤ (0 : Int) + d234 p := by
  cases selected : p 106 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d186, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1515 p hg
    simpa only [d186, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d186, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1517 p hg
    simpa only [d186, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1519 (p : Pattern) (guard : d0 p = 1) : d196 p ≤ (0 : Int) + d150 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1520 (p : Pattern) (guard : d866 p = 1) : d197 p ≤ (0 : Int) + d235 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d197, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d866, d197, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d197, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1519 p hg
    simpa only [d866, d197, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1521 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d236 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1522 (p : Pattern) (guard : d868 p = 1) : d198 p ≤ (0 : Int) + d237 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d198, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1520 p hg
    simpa only [d868, d198, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d198, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1521 p hg
    simpa only [d868, d198, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1523 (p : Pattern) (guard : d0 p = 1) : d203 p ≤ (0 : Int) + d161 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1524 (p : Pattern) (guard : d866 p = 1) : d204 p ≤ (0 : Int) + d238 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d204, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare429 p hg
    simpa only [d866, d204, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d204, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1523 p hg
    simpa only [d866, d204, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1525 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (0 : Int) + d239 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1526 (p : Pattern) (guard : d868 p = 1) : d205 p ≤ (0 : Int) + d240 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d205, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1524 p hg
    simpa only [d868, d205, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d205, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1525 p hg
    simpa only [d868, d205, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1527 (p : Pattern) (guard : d868 p = 1) : d206 p ≤ (0 : Int) + d241 p := by
  cases selected : p 106 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d206, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1522 p hg
    simpa only [d206, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d206, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1526 p hg
    simpa only [d206, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1528 (p : Pattern) (guard : d868 p = 1) : d207 p ≤ (0 : Int) + d242 p := by
  cases selected : p 86 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d207, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1518 p hg
    simpa only [d207, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d207, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1527 p hg
    simpa only [d207, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1529 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d243 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1530 (p : Pattern) (guard : d868 p = 1) : d208 p ≤ (0 : Int) + d244 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d208, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare483 p hg
    simpa only [d868, d208, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d208, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1529 p hg
    simpa only [d868, d208, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1531 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (0 : Int) + d245 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1532 (p : Pattern) (guard : d868 p = 1) : d209 p ≤ (0 : Int) + d246 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d209, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare487 p hg
    simpa only [d868, d209, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d209, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1531 p hg
    simpa only [d868, d209, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1533 (p : Pattern) (guard : d868 p = 1) : d210 p ≤ (0 : Int) + d247 p := by
  cases selected : p 106 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d210, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1530 p hg
    simpa only [d210, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d210, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1532 p hg
    simpa only [d210, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1534 (p : Pattern) (guard : d0 p = 1) : d214 p ≤ (0 : Int) + d161 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1535 (p : Pattern) (guard : d866 p = 1) : d215 p ≤ (0 : Int) + d248 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d215, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d866, d215, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d215, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1534 p hg
    simpa only [d866, d215, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1536 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (0 : Int) + d249 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1537 (p : Pattern) (guard : d868 p = 1) : d216 p ≤ (0 : Int) + d250 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d216, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1535 p hg
    simpa only [d868, d216, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d216, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1536 p hg
    simpa only [d868, d216, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1538 (p : Pattern) (guard : d0 p = 1) : d222 p ≤ (0 : Int) + d167 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1539 (p : Pattern) (guard : d866 p = 1) : d223 p ≤ (0 : Int) + d251 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d223, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare429 p hg
    simpa only [d866, d223, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d223, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1538 p hg
    simpa only [d866, d223, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
