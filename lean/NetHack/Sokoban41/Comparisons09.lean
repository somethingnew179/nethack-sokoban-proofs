/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons08
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c1440 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (14 : Int) + d10 pattern := by
  change (4 : Int) ≤ (14 : Int) + 10
  decide
theorem c1441 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (14 : Int) + d10 pattern := by
  change (5 : Int) ≤ (14 : Int) + 10
  decide
theorem c1442 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1440 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1441 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1443 (pattern : Ten) (guard : d1 pattern = 1) : d197 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1442 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1444 (pattern : Ten) (guard : d1 pattern = 1) : d202 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1439 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1443 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1445 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (14 : Int) + d10 pattern := by
  change (6 : Int) ≤ (14 : Int) + 10
  decide
theorem c1446 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (14 : Int) + d10 pattern := by
  change (7 : Int) ≤ (14 : Int) + 10
  decide
theorem c1447 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1445 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1446 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1448 (pattern : Ten) (guard : d1 pattern = 1) : d198 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1447 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1449 (pattern : Ten) (guard : d1 pattern = 1) : d203 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1448 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1450 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1444 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1449 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1451 (pattern : Ten) (guard : d1 pattern = 1) : d310 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1437 pattern childGuard
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1440 pattern childGuard
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1452 (pattern : Ten) (guard : d1 pattern = 1) : d314 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1438 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1451 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1453 (pattern : Ten) (guard : d1 pattern = 1) : d311 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1441 pattern childGuard
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1445 pattern childGuard
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1454 (pattern : Ten) (guard : d1 pattern = 1) : d315 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1442 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1453 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1455 (pattern : Ten) (guard : d1 pattern = 1) : d320 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1452 pattern childGuard
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1454 pattern childGuard
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1456 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (14 : Int) + d10 pattern := by
  change (8 : Int) ≤ (14 : Int) + 10
  decide
theorem c1457 (pattern : Ten) (guard : d1 pattern = 1) : d312 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1446 pattern childGuard
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1456 pattern childGuard
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1458 (pattern : Ten) (guard : d1 pattern = 1) : d316 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1447 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1457 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1459 (pattern : Ten) (guard : d1 pattern = 1) : d319 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1458 pattern childGuard
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1460 (pattern : Ten) (guard : d1 pattern = 1) : d323 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1455 pattern childGuard
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1461 (pattern : Ten) (guard : d1 pattern = 1) : d195 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1456 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1411 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1462 (pattern : Ten) (guard : d1 pattern = 1) : d11 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1411 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1463 (pattern : Ten) (guard : d1 pattern = 1) : d196 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1461 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1462 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1464 (pattern : Ten) (guard : d1 pattern = 1) : d201 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1463 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1465 (pattern : Ten) (guard : d1 pattern = 1) : d206 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1464 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1466 (pattern : Ten) (guard : d1 pattern = 1) : d325 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1460 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1465 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1467 (pattern : Ten) (guard : d1 pattern = 1) : d344 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1450 pattern childGuard
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1466 pattern childGuard
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1468 (pattern : Ten) (guard : d1 pattern = 1) : d341 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1454 pattern childGuard
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1458 pattern childGuard
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1469 (pattern : Ten) (guard : d1 pattern = 1) : d342 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1468 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1464 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1470 (pattern : Ten) (guard : d1 pattern = 1) : d343 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1469 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1471 (pattern : Ten) (guard : d1 pattern = 1) : d345 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1450 pattern childGuard
    simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1470 pattern childGuard
    simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1472 (pattern : Ten) (guard : d1 pattern = 1) : d346 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1467 pattern childGuard
    simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1471 pattern childGuard
    simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1473 (pattern : Ten) (guard : d1 pattern = 1) : d309 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1434 pattern childGuard
    simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1436 pattern childGuard
    simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1474 (pattern : Ten) (guard : d1 pattern = 1) : d313 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1435 pattern childGuard
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1473 pattern childGuard
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1475 (pattern : Ten) (guard : d1 pattern = 1) : d317 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1474 pattern childGuard
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1452 pattern childGuard
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1476 (pattern : Ten) (guard : d1 pattern = 1) : d318 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1454 pattern childGuard
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1477 (pattern : Ten) (guard : d1 pattern = 1) : d321 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1475 pattern childGuard
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1476 pattern childGuard
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1478 (pattern : Ten) (guard : d1 pattern = 1) : d322 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1479 (pattern : Ten) (guard : d1 pattern = 1) : d324 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1477 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1478 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1480 (pattern : Ten) (guard : d1 pattern = 1) : d333 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1479 pattern childGuard
    simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1481 (pattern : Ten) (guard : d1 pattern = 1) : d334 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1466 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1482 (pattern : Ten) (guard : d1 pattern = 1) : d336 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1480 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1481 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1483 (pattern : Ten) (guard : d1 pattern = 1) : d347 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1472 pattern childGuard
    simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1482 pattern childGuard
    simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1484 (pattern : Ten) (guard : d1 pattern = 1) : d200 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1461 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1485 (pattern : Ten) (guard : d1 pattern = 1) : d205 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1484 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1486 (pattern : Ten) (guard : d1 pattern = 1) : d209 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1485 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1487 (pattern : Ten) (guard : d1 pattern = 1) : d214 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1486 pattern childGuard
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1488 (pattern : Ten) (guard : d1 pattern = 1) : d210 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1465 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1489 (pattern : Ten) (guard : d1 pattern = 1) : d335 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1488 pattern childGuard
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1490 (pattern : Ten) (guard : d1 pattern = 1) : d337 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1489 pattern childGuard
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1491 (pattern : Ten) (guard : d1 pattern = 1) : d348 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1487 pattern childGuard
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1490 pattern childGuard
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1492 (pattern : Ten) (guard : d1 pattern = 1) : d349 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1483 pattern childGuard
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1491 pattern childGuard
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1493 (pattern : Ten) (guard : d350 pattern = 1) : d349 pattern ≤ (1 : Int) + d349 pattern := by
  omega
theorem c1494 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (19 : Int) + d0 pattern := by
  omega
theorem c1495 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (19 : Int) + d1 pattern := by
  change (0 : Int) ≤ (19 : Int) + 1
  decide
theorem c1496 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (19 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1494 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1495 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1497 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (19 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1498 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (19 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1496 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1497 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1499 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (19 : Int) + d2 pattern := by
  omega
theorem c1500 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (19 : Int) + d3 pattern := by
  change (2 : Int) ≤ (19 : Int) + 3
  decide
theorem c1501 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (19 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1499 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1500 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1502 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (19 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1503 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (19 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1501 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1502 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1504 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (19 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1498 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1503 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1505 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (19 : Int) + d4 pattern := by
  omega
theorem c1506 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (19 : Int) + d5 pattern := by
  change (4 : Int) ≤ (19 : Int) + 5
  decide
theorem c1507 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (19 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1505 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1506 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1508 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (19 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1509 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (19 : Int) + d193 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1507 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1508 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1510 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (19 : Int) + d10 pattern := by
  omega
theorem c1511 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (19 : Int) + d197 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1509 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1512 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (19 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1504 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1511 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1513 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (19 : Int) + d6 pattern := by
  omega
theorem c1514 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (19 : Int) + d7 pattern := by
  change (6 : Int) ≤ (19 : Int) + 7
  decide
theorem c1515 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (19 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1513 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1514 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1516 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (19 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1517 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (19 : Int) + d194 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1515 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1516 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1518 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (19 : Int) + d198 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1517 pattern childGuard
    simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1519 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (19 : Int) + d203 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1518 pattern childGuard
    simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1520 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (19 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1512 pattern childGuard
    simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1519 pattern childGuard
    simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1521 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (19 : Int) + d310 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1522 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (19 : Int) + d314 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1501 pattern childGuard
    simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1521 pattern childGuard
    simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1523 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (19 : Int) + d311 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1524 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (19 : Int) + d315 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1507 pattern childGuard
    simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1523 pattern childGuard
    simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1525 (pattern : Ten) (guard : d350 pattern = 1) : d44 pattern ≤ (19 : Int) + d320 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1522 pattern childGuard
    simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1524 pattern childGuard
    simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1526 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (19 : Int) + d312 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1527 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (19 : Int) + d316 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1515 pattern childGuard
    simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1526 pattern childGuard
    simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1528 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (19 : Int) + d319 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1527 pattern childGuard
    simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1529 (pattern : Ten) (guard : d350 pattern = 1) : d50 pattern ≤ (19 : Int) + d323 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1525 pattern childGuard
    simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1528 pattern childGuard
    simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1530 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (19 : Int) + d8 pattern := by
  omega
theorem c1531 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (19 : Int) + d9 pattern := by
  change (8 : Int) ≤ (19 : Int) + 9
  decide
theorem c1532 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (19 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1530 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1531 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1533 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (19 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1534 (pattern : Ten) (guard : d350 pattern = 1) : d8 pattern ≤ (19 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1532 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1533 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1535 (pattern : Ten) (guard : d350 pattern = 1) : d45 pattern ≤ (19 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1534 pattern childGuard
    simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1536 (pattern : Ten) (guard : d350 pattern = 1) : d51 pattern ≤ (19 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1535 pattern childGuard
    simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1537 (pattern : Ten) (guard : d350 pattern = 1) : d55 pattern ≤ (19 : Int) + d325 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1529 pattern childGuard
    simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1536 pattern childGuard
    simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1538 (pattern : Ten) (guard : d350 pattern = 1) : d160 pattern ≤ (19 : Int) + d344 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1520 pattern childGuard
    simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1537 pattern childGuard
    simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1539 (pattern : Ten) (guard : d350 pattern = 1) : d157 pattern ≤ (19 : Int) + d341 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1524 pattern childGuard
    simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1527 pattern childGuard
    simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1540 (pattern : Ten) (guard : d350 pattern = 1) : d158 pattern ≤ (19 : Int) + d342 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1539 pattern childGuard
    simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1535 pattern childGuard
    simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1541 (pattern : Ten) (guard : d350 pattern = 1) : d159 pattern ≤ (19 : Int) + d343 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1540 pattern childGuard
    simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1542 (pattern : Ten) (guard : d350 pattern = 1) : d161 pattern ≤ (19 : Int) + d345 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1520 pattern childGuard
    simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1541 pattern childGuard
    simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1543 (pattern : Ten) (guard : d350 pattern = 1) : d165 pattern ≤ (19 : Int) + d346 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1538 pattern childGuard
    simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1542 pattern childGuard
    simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1544 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (19 : Int) + d309 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1545 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (19 : Int) + d313 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1496 pattern childGuard
    simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1544 pattern childGuard
    simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1546 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (19 : Int) + d317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1545 pattern childGuard
    simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1522 pattern childGuard
    simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1547 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (19 : Int) + d318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1524 pattern childGuard
    simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1548 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (19 : Int) + d321 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1546 pattern childGuard
    simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1547 pattern childGuard
    simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1549 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (19 : Int) + d322 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1528 pattern childGuard
    simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1550 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (19 : Int) + d324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1548 pattern childGuard
    simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1549 pattern childGuard
    simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1551 (pattern : Ten) (guard : d350 pattern = 1) : d162 pattern ≤ (19 : Int) + d333 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1550 pattern childGuard
    simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1552 (pattern : Ten) (guard : d350 pattern = 1) : d163 pattern ≤ (19 : Int) + d334 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1537 pattern childGuard
    simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1553 (pattern : Ten) (guard : d350 pattern = 1) : d166 pattern ≤ (19 : Int) + d336 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1551 pattern childGuard
    simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1552 pattern childGuard
    simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1554 (pattern : Ten) (guard : d350 pattern = 1) : d168 pattern ≤ (19 : Int) + d347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1543 pattern childGuard
    simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1553 pattern childGuard
    simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1555 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (19 : Int) + d8 pattern := by
  change (7 : Int) ≤ (19 : Int) + 8
  decide
theorem c1556 (pattern : Ten) (guard : d1 pattern = 1) : d38 pattern ≤ (19 : Int) + d8 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1555 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1530 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1557 (pattern : Ten) (guard : d1 pattern = 1) : d40 pattern ≤ (19 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1556 pattern childGuard
    simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1531 pattern childGuard
    simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1558 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (19 : Int) + d195 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1559 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (19 : Int) + d195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1557 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1558 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1560 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (19 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1559 pattern childGuard
    simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1561 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (19 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1562 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (19 : Int) + d209 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1561 pattern childGuard
    simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1563 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (19 : Int) + d10 pattern := by
  change (9 : Int) ≤ (19 : Int) + 10
  decide
theorem c1564 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (19 : Int) + d10 pattern := by
  omega
theorem c1565 (pattern : Ten) (guard : d1 pattern = 1) : d39 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1563 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1566 (pattern : Ten) (guard : d1 pattern = 1) : d41 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1565 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1567 (pattern : Ten) (guard : d0 pattern = 1) : d41 pattern ≤ (19 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1568 (pattern : Ten) (guard : d350 pattern = 1) : d41 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1566 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1569 (pattern : Ten) (guard : d350 pattern = 1) : d47 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1568 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1570 (pattern : Ten) (guard : d350 pattern = 1) : d53 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1569 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1571 (pattern : Ten) (guard : d350 pattern = 1) : d57 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1570 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1572 (pattern : Ten) (guard : d350 pattern = 1) : d164 pattern ≤ (19 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1562 pattern childGuard
    simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1571 pattern childGuard
    simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1573 (pattern : Ten) (guard : d350 pattern = 1) : d60 pattern ≤ (19 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1562 pattern childGuard
    simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1574 (pattern : Ten) (guard : d350 pattern = 1) : d167 pattern ≤ (19 : Int) + d214 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1572 pattern childGuard
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1573 pattern childGuard
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1575 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (19 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1576 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (19 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1557 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1575 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1577 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (19 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1576 pattern childGuard
    simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1578 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (19 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1577 pattern childGuard
    simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1579 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (19 : Int) + d210 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1578 pattern childGuard
    simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1580 (pattern : Ten) (guard : d350 pattern = 1) : d60 pattern ≤ (19 : Int) + d335 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1579 pattern childGuard
    simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1581 (pattern : Ten) (guard : d350 pattern = 1) : d61 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1571 pattern childGuard
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1582 (pattern : Ten) (guard : d350 pattern = 1) : d63 pattern ≤ (19 : Int) + d337 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1580 pattern childGuard
    simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1581 pattern childGuard
    simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1583 (pattern : Ten) (guard : d350 pattern = 1) : d169 pattern ≤ (19 : Int) + d348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1574 pattern childGuard
    simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1582 pattern childGuard
    simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1584 (pattern : Ten) (guard : d350 pattern = 1) : d170 pattern ≤ (19 : Int) + d349 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1554 pattern childGuard
    simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1583 pattern childGuard
    simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1585 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (19 : Int) + d10 pattern := by
  change (0 : Int) ≤ (19 : Int) + 10
  decide
theorem c1586 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (19 : Int) + d10 pattern := by
  change (1 : Int) ≤ (19 : Int) + 10
  decide
theorem c1587 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1585 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1586 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1588 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (19 : Int) + d10 pattern := by
  change (2 : Int) ≤ (19 : Int) + 10
  decide
theorem c1589 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (19 : Int) + d10 pattern := by
  change (3 : Int) ≤ (19 : Int) + 10
  decide
theorem c1590 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1588 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1589 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1591 (pattern : Ten) (guard : d1 pattern = 1) : d174 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1587 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1590 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1592 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (19 : Int) + d10 pattern := by
  change (4 : Int) ≤ (19 : Int) + 10
  decide
theorem c1593 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (19 : Int) + d10 pattern := by
  change (5 : Int) ≤ (19 : Int) + 10
  decide
theorem c1594 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1592 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1593 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1595 (pattern : Ten) (guard : d1 pattern = 1) : d197 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1594 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1596 (pattern : Ten) (guard : d1 pattern = 1) : d202 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1591 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1595 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1597 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (19 : Int) + d10 pattern := by
  change (6 : Int) ≤ (19 : Int) + 10
  decide
theorem c1598 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (19 : Int) + d10 pattern := by
  change (7 : Int) ≤ (19 : Int) + 10
  decide
theorem c1599 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1597 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1598 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
