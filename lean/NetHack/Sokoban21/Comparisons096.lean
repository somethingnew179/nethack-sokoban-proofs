/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons095
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c13440 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (2 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13418 pattern childGuard
    simpa only [d817, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13439 pattern childGuard
    simpa only [d817, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13441 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (2 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13333 pattern childGuard
    simpa only [d41, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13305 pattern childGuard
    simpa only [d41, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13442 (pattern : Twelve) (guard : d1 pattern = 1) : d1291 pattern ≤ (2 : Int) + d1283 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13440 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13441 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13443 (pattern : Twelve) (guard : d1 pattern = 1) : d1303 pattern ≤ (2 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13442 pattern childGuard
    simpa only [d1303, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1303, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13444 (pattern : Twelve) (guard : d1 pattern = 1) : d1311 pattern ≤ (2 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13417 pattern childGuard
    simpa only [d1311, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13443 pattern childGuard
    simpa only [d1311, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13445 (pattern : Twelve) (guard : d1 pattern = 1) : d1292 pattern ≤ (2 : Int) + d1290 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13374 pattern childGuard
    simpa only [d1292, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13343 pattern childGuard
    simpa only [d1292, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13446 (pattern : Twelve) (guard : d1 pattern = 1) : d1304 pattern ≤ (2 : Int) + d1302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13445 pattern childGuard
    simpa only [d1304, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1304, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13447 (pattern : Twelve) (guard : d1 pattern = 1) : d1312 pattern ≤ (2 : Int) + d1310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13428 pattern childGuard
    simpa only [d1312, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13446 pattern childGuard
    simpa only [d1312, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13448 (pattern : Twelve) (guard : d1 pattern = 1) : d1317 pattern ≤ (2 : Int) + d1316 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13444 pattern childGuard
    simpa only [d1317, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13447 pattern childGuard
    simpa only [d1317, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13449 (pattern : Twelve) (guard : d0 pattern = 1) : d1318 pattern ≤ (2 : Int) + d1316 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13450 (pattern : Twelve) (guard : d1835 pattern = 1) : d1320 pattern ≤ (2 : Int) + d1316 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13448 pattern childGuard
    simpa only [d1835, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13449 pattern childGuard
    simpa only [d1835, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13451 (pattern : Twelve) (guard : d2266 pattern = 1) : d1322 pattern ≤ (2 : Int) + d1316 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13436 pattern childGuard
    simpa only [d2266, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13450 pattern childGuard
    simpa only [d2266, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13452 (pattern : Twelve) (guard : d2266 pattern = 1) : d1323 pattern ≤ (2 : Int) + d2269 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2266 pattern = 1 := by simpa only [d1323, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13435 pattern childGuard
    simpa only [d1323, d2269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2266 pattern = 1 := by simpa only [d1323, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13451 pattern childGuard
    simpa only [d1323, d2269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13453 (pattern : Twelve) (guard : d0 pattern = 1) : d1660 pattern ≤ (2 : Int) + d1660 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13454 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (2 : Int) + d1324 pattern := by
  omega
theorem c13455 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (2 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13308 pattern childGuard
    simpa only [d20, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13370 pattern childGuard
    simpa only [d20, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13456 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (2 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13454 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13455 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13457 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (2 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13419 pattern childGuard
    simpa only [d1652, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13456 pattern childGuard
    simpa only [d1652, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13458 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (2 : Int) + d25 pattern := by
  omega
theorem c13459 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13458 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13373 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13460 (pattern : Twelve) (guard : d1 pattern = 1) : d1653 pattern ≤ (2 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13459 pattern childGuard
    simpa only [d1653, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1653, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13461 (pattern : Twelve) (guard : d1 pattern = 1) : d1658 pattern ≤ (2 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13457 pattern childGuard
    simpa only [d1658, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13460 pattern childGuard
    simpa only [d1658, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13462 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13369 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13463 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (2 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13372 pattern childGuard
    simpa only [d22, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13462 pattern childGuard
    simpa only [d22, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13464 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (2 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13455 pattern childGuard
    simpa only [d1646, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13463 pattern childGuard
    simpa only [d1646, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13465 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (2 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13455 pattern childGuard
    simpa only [d128, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d128, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13466 (pattern : Twelve) (guard : d1 pattern = 1) : d1648 pattern ≤ (2 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13464 pattern childGuard
    simpa only [d1648, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13465 pattern childGuard
    simpa only [d1648, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13467 (pattern : Twelve) (guard : d1 pattern = 1) : d1654 pattern ≤ (2 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13429 pattern childGuard
    simpa only [d1654, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13466 pattern childGuard
    simpa only [d1654, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13468 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13371 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13469 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13462 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13468 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13470 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (2 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13373 pattern childGuard
    simpa only [d822, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13469 pattern childGuard
    simpa only [d822, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13471 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (2 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13470 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13375 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13472 (pattern : Twelve) (guard : d1 pattern = 1) : d1655 pattern ≤ (2 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13471 pattern childGuard
    simpa only [d1655, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1655, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13473 (pattern : Twelve) (guard : d1 pattern = 1) : d1659 pattern ≤ (2 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13467 pattern childGuard
    simpa only [d1659, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13472 pattern childGuard
    simpa only [d1659, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13474 (pattern : Twelve) (guard : d1 pattern = 1) : d1661 pattern ≤ (2 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13461 pattern childGuard
    simpa only [d1661, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13473 pattern childGuard
    simpa only [d1661, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13475 (pattern : Twelve) (guard : d0 pattern = 1) : d1662 pattern ≤ (2 : Int) + d1660 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13476 (pattern : Twelve) (guard : d1835 pattern = 1) : d1663 pattern ≤ (2 : Int) + d1660 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13474 pattern childGuard
    simpa only [d1835, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13475 pattern childGuard
    simpa only [d1835, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13477 (pattern : Twelve) (guard : d2266 pattern = 1) : d1664 pattern ≤ (2 : Int) + d1660 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13453 pattern childGuard
    simpa only [d2266, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13476 pattern childGuard
    simpa only [d2266, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13478 (pattern : Twelve) (guard : d0 pattern = 1) : d110 pattern ≤ (2 : Int) + d2271 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13479 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d3 pattern := by
  change (2 : Int) ≤ (2 : Int) + 3
  decide
theorem c13480 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d5 pattern := by
  change (2 : Int) ≤ (2 : Int) + 5
  decide
theorem c13481 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13479 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13480 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13482 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d4 pattern := by
  change (2 : Int) ≤ (2 : Int) + 4
  decide
theorem c13483 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d6 pattern := by
  change (2 : Int) ≤ (2 : Int) + 6
  decide
theorem c13484 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13483 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13485 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13481 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13484 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13486 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (2 : Int) + d31 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d30, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13485 pattern childGuard
    simpa only [d30, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13487 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (2 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13486 pattern childGuard
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13488 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d4 pattern := by
  change (3 : Int) ≤ (2 : Int) + 4
  decide
theorem c13489 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d6 pattern := by
  change (3 : Int) ≤ (2 : Int) + 6
  decide
theorem c13490 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13488 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13489 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13491 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d5 pattern := by
  change (3 : Int) ≤ (2 : Int) + 5
  decide
theorem c13492 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13491 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13489 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13493 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13490 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13492 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13494 (pattern : Twelve) (guard : d1 pattern = 1) : d37 pattern ≤ (2 : Int) + d32 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d37, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13493 pattern childGuard
    simpa only [d37, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13495 (pattern : Twelve) (guard : d1 pattern = 1) : d58 pattern ≤ (2 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d58, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13494 pattern childGuard
    simpa only [d58, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13496 (pattern : Twelve) (guard : d1 pattern = 1) : d79 pattern ≤ (2 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13487 pattern childGuard
    simpa only [d79, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13495 pattern childGuard
    simpa only [d79, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13497 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13480 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13483 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13498 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13497 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13483 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13499 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (2 : Int) + d33 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d30, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13498 pattern childGuard
    simpa only [d30, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13500 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (2 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13499 pattern childGuard
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13501 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (2 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13500 pattern childGuard
    simpa only [d80, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13290 pattern childGuard
    simpa only [d80, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13502 (pattern : Twelve) (guard : d1 pattern = 1) : d95 pattern ≤ (2 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13496 pattern childGuard
    simpa only [d95, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13501 pattern childGuard
    simpa only [d95, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13503 (pattern : Twelve) (guard : d0 pattern = 1) : d96 pattern ≤ (2 : Int) + d92 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13504 (pattern : Twelve) (guard : d1844 pattern = 1) : d104 pattern ≤ (2 : Int) + d92 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13502 pattern childGuard
    simpa only [d1844, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13503 pattern childGuard
    simpa only [d1844, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13505 (pattern : Twelve) (guard : d1 pattern = 1) : d94 pattern ≤ (2 : Int) + d94 pattern := by
  omega
theorem c13506 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d94 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13507 (pattern : Twelve) (guard : d1844 pattern = 1) : d105 pattern ≤ (2 : Int) + d94 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13505 pattern childGuard
    simpa only [d1844, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13506 pattern childGuard
    simpa only [d1844, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13508 (pattern : Twelve) (guard : d1844 pattern = 1) : d111 pattern ≤ (2 : Int) + d2271 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d111, d2271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13504 pattern childGuard
    simpa only [d111, d2271, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d111, d2271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13507 pattern childGuard
    simpa only [d111, d2271, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13509 (pattern : Twelve) (guard : d2270 pattern = 1) : d114 pattern ≤ (2 : Int) + d2271 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13478 pattern childGuard
    simpa only [d2270, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13508 pattern childGuard
    simpa only [d2270, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13510 (pattern : Twelve) (guard : d0 pattern = 1) : d112 pattern ≤ (2 : Int) + d2272 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13511 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (2 : Int) + d43 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13320 pattern childGuard
    simpa only [d46, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13493 pattern childGuard
    simpa only [d46, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13512 (pattern : Twelve) (guard : d1 pattern = 1) : d67 pattern ≤ (2 : Int) + d62 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d67, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13511 pattern childGuard
    simpa only [d67, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13513 (pattern : Twelve) (guard : d1 pattern = 1) : d87 pattern ≤ (2 : Int) + d83 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13487 pattern childGuard
    simpa only [d87, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13512 pattern childGuard
    simpa only [d87, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13514 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d5 pattern := by
  change (4 : Int) ≤ (2 : Int) + 5
  decide
theorem c13515 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d6 pattern := by
  change (4 : Int) ≤ (2 : Int) + 6
  decide
theorem c13516 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13514 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13515 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13517 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13516 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13515 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13518 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (2 : Int) + d44 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d38, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13517 pattern childGuard
    simpa only [d38, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13519 (pattern : Twelve) (guard : d1 pattern = 1) : d68 pattern ≤ (2 : Int) + d63 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d68, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13518 pattern childGuard
    simpa only [d68, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13520 (pattern : Twelve) (guard : d1 pattern = 1) : d64 pattern ≤ (2 : Int) + d64 pattern := by
  omega
theorem c13521 (pattern : Twelve) (guard : d1 pattern = 1) : d88 pattern ≤ (2 : Int) + d84 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13519 pattern childGuard
    simpa only [d88, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13520 pattern childGuard
    simpa only [d88, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13522 (pattern : Twelve) (guard : d1 pattern = 1) : d100 pattern ≤ (2 : Int) + d98 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13513 pattern childGuard
    simpa only [d100, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13521 pattern childGuard
    simpa only [d100, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13523 (pattern : Twelve) (guard : d0 pattern = 1) : d101 pattern ≤ (2 : Int) + d98 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13524 (pattern : Twelve) (guard : d1844 pattern = 1) : d108 pattern ≤ (2 : Int) + d98 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13522 pattern childGuard
    simpa only [d1844, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13523 pattern childGuard
    simpa only [d1844, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13525 (pattern : Twelve) (guard : d1 pattern = 1) : d99 pattern ≤ (2 : Int) + d99 pattern := by
  omega
theorem c13526 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d99 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13527 (pattern : Twelve) (guard : d1844 pattern = 1) : d109 pattern ≤ (2 : Int) + d99 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13525 pattern childGuard
    simpa only [d1844, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13526 pattern childGuard
    simpa only [d1844, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13528 (pattern : Twelve) (guard : d1844 pattern = 1) : d113 pattern ≤ (2 : Int) + d2272 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d113, d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13524 pattern childGuard
    simpa only [d113, d2272, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d113, d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13527 pattern childGuard
    simpa only [d113, d2272, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13529 (pattern : Twelve) (guard : d2270 pattern = 1) : d115 pattern ≤ (2 : Int) + d2272 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13510 pattern childGuard
    simpa only [d2270, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13528 pattern childGuard
    simpa only [d2270, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13530 (pattern : Twelve) (guard : d2270 pattern = 1) : d116 pattern ≤ (2 : Int) + d2273 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2270 pattern = 1 := by simpa only [d116, d2273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13509 pattern childGuard
    simpa only [d116, d2273, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2270 pattern = 1 := by simpa only [d116, d2273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13529 pattern childGuard
    simpa only [d116, d2273, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13531 (pattern : Twelve) (guard : d0 pattern = 1) : d861 pattern ≤ (2 : Int) + d854 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13532 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (2 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d30, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13483 pattern childGuard
    simpa only [d30, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13533 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (2 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13532 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13534 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (2 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13356 pattern childGuard
    simpa only [d819, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13489 pattern childGuard
    simpa only [d819, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13535 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (2 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13328 pattern childGuard
    simpa only [d828, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13534 pattern childGuard
    simpa only [d828, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13536 (pattern : Twelve) (guard : d1 pattern = 1) : d842 pattern ≤ (2 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13533 pattern childGuard
    simpa only [d842, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13535 pattern childGuard
    simpa only [d842, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13537 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13483 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13489 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13538 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13483 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13537 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13539 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (2 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d34, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13538 pattern childGuard
    simpa only [d34, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13540 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (2 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13328 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13539 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13541 (pattern : Twelve) (guard : d1 pattern = 1) : d843 pattern ≤ (2 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13540 pattern childGuard
    simpa only [d843, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13361 pattern childGuard
    simpa only [d843, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13542 (pattern : Twelve) (guard : d1 pattern = 1) : d855 pattern ≤ (2 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13536 pattern childGuard
    simpa only [d855, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13541 pattern childGuard
    simpa only [d855, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13543 (pattern : Twelve) (guard : d0 pattern = 1) : d856 pattern ≤ (2 : Int) + d854 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13544 (pattern : Twelve) (guard : d1844 pattern = 1) : d862 pattern ≤ (2 : Int) + d854 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13542 pattern childGuard
    simpa only [d1844, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13543 pattern childGuard
    simpa only [d1844, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13545 (pattern : Twelve) (guard : d1 pattern = 1) : d854 pattern ≤ (2 : Int) + d854 pattern := by
  omega
theorem c13546 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d854 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13547 (pattern : Twelve) (guard : d1844 pattern = 1) : d863 pattern ≤ (2 : Int) + d854 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13545 pattern childGuard
    simpa only [d1844, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13546 pattern childGuard
    simpa only [d1844, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13548 (pattern : Twelve) (guard : d1844 pattern = 1) : d867 pattern ≤ (2 : Int) + d854 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13544 pattern childGuard
    simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13547 pattern childGuard
    simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13549 (pattern : Twelve) (guard : d2270 pattern = 1) : d869 pattern ≤ (2 : Int) + d854 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13531 pattern childGuard
    simpa only [d2270, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13548 pattern childGuard
    simpa only [d2270, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13550 (pattern : Twelve) (guard : d0 pattern = 1) : d864 pattern ≤ (2 : Int) + d858 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13551 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (2 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13320 pattern childGuard
    simpa only [d46, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13489 pattern childGuard
    simpa only [d46, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13552 (pattern : Twelve) (guard : d1 pattern = 1) : d834 pattern ≤ (2 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13328 pattern childGuard
    simpa only [d834, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13551 pattern childGuard
    simpa only [d834, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13553 (pattern : Twelve) (guard : d1 pattern = 1) : d849 pattern ≤ (2 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13533 pattern childGuard
    simpa only [d849, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13552 pattern childGuard
    simpa only [d849, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13554 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (2 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d38, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13515 pattern childGuard
    simpa only [d38, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13555 (pattern : Twelve) (guard : d1 pattern = 1) : d835 pattern ≤ (2 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13328 pattern childGuard
    simpa only [d835, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13554 pattern childGuard
    simpa only [d835, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13556 (pattern : Twelve) (guard : d1 pattern = 1) : d850 pattern ≤ (2 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13555 pattern childGuard
    simpa only [d850, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13361 pattern childGuard
    simpa only [d850, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13557 (pattern : Twelve) (guard : d1 pattern = 1) : d859 pattern ≤ (2 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13553 pattern childGuard
    simpa only [d859, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13556 pattern childGuard
    simpa only [d859, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13558 (pattern : Twelve) (guard : d0 pattern = 1) : d860 pattern ≤ (2 : Int) + d858 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13559 (pattern : Twelve) (guard : d1844 pattern = 1) : d865 pattern ≤ (2 : Int) + d858 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13557 pattern childGuard
    simpa only [d1844, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13558 pattern childGuard
    simpa only [d1844, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13560 (pattern : Twelve) (guard : d1 pattern = 1) : d858 pattern ≤ (2 : Int) + d858 pattern := by
  omega
theorem c13561 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d858 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13562 (pattern : Twelve) (guard : d1844 pattern = 1) : d866 pattern ≤ (2 : Int) + d858 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13560 pattern childGuard
    simpa only [d1844, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13561 pattern childGuard
    simpa only [d1844, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13563 (pattern : Twelve) (guard : d1844 pattern = 1) : d868 pattern ≤ (2 : Int) + d858 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13559 pattern childGuard
    simpa only [d868, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13562 pattern childGuard
    simpa only [d868, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13564 (pattern : Twelve) (guard : d2270 pattern = 1) : d870 pattern ≤ (2 : Int) + d858 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13550 pattern childGuard
    simpa only [d2270, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13563 pattern childGuard
    simpa only [d2270, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13565 (pattern : Twelve) (guard : d2270 pattern = 1) : d871 pattern ≤ (2 : Int) + d2274 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2270 pattern = 1 := by simpa only [d871, d2274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13549 pattern childGuard
    simpa only [d871, d2274, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2270 pattern = 1 := by simpa only [d871, d2274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13564 pattern childGuard
    simpa only [d871, d2274, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13566 (pattern : Twelve) (guard : d0 pattern = 1) : d1313 pattern ≤ (2 : Int) + d1306 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13567 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (2 : Int) + d1279 pattern := by
  omega
theorem c13568 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13489 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13515 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13569 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13489 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13568 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13570 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (2 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13413 pattern childGuard
    simpa only [d1281, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13569 pattern childGuard
    simpa only [d1281, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13571 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (2 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13567 pattern childGuard
    simpa only [d1287, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13570 pattern childGuard
    simpa only [d1287, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13572 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (2 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13540 pattern childGuard
    simpa only [d1297, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13571 pattern childGuard
    simpa only [d1297, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13573 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (2 : Int) + d817 pattern := by
  omega
theorem c13574 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13483 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13515 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13575 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (2 : Int) + d6 pattern := by
  change (5 : Int) ≤ (2 : Int) + 6
  decide
theorem c13576 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13489 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13575 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13577 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13574 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13576 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13578 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (2 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13418 pattern childGuard
    simpa only [d817, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13577 pattern childGuard
    simpa only [d817, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13579 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (2 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13573 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13578 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
