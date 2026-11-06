/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons096
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c13580 (pattern : Twelve) (guard : d1 pattern = 1) : d1298 pattern ≤ (2 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13579 pattern childGuard
    simpa only [d1298, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1298, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13581 (pattern : Twelve) (guard : d1 pattern = 1) : d1307 pattern ≤ (2 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13572 pattern childGuard
    simpa only [d1307, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13580 pattern childGuard
    simpa only [d1307, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13582 (pattern : Twelve) (guard : d0 pattern = 1) : d1308 pattern ≤ (2 : Int) + d1306 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13583 (pattern : Twelve) (guard : d1844 pattern = 1) : d1314 pattern ≤ (2 : Int) + d1306 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13581 pattern childGuard
    simpa only [d1844, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13582 pattern childGuard
    simpa only [d1844, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13584 (pattern : Twelve) (guard : d1 pattern = 1) : d1306 pattern ≤ (2 : Int) + d1306 pattern := by
  omega
theorem c13585 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d1306 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13586 (pattern : Twelve) (guard : d1844 pattern = 1) : d1315 pattern ≤ (2 : Int) + d1306 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13584 pattern childGuard
    simpa only [d1844, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13585 pattern childGuard
    simpa only [d1844, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13587 (pattern : Twelve) (guard : d1844 pattern = 1) : d1319 pattern ≤ (2 : Int) + d1306 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13583 pattern childGuard
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13586 pattern childGuard
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13588 (pattern : Twelve) (guard : d2270 pattern = 1) : d1321 pattern ≤ (2 : Int) + d1306 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13566 pattern childGuard
    simpa only [d2270, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13587 pattern childGuard
    simpa only [d2270, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13589 (pattern : Twelve) (guard : d0 pattern = 1) : d1316 pattern ≤ (2 : Int) + d1310 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13590 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (2 : Int) + d23 pattern := by
  omega
theorem c13591 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13515 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13575 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13592 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13515 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13591 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13593 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (2 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13590 pattern childGuard
    simpa only [d41, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13592 pattern childGuard
    simpa only [d41, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13594 (pattern : Twelve) (guard : d1 pattern = 1) : d1291 pattern ≤ (2 : Int) + d1290 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13573 pattern childGuard
    simpa only [d1291, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13593 pattern childGuard
    simpa only [d1291, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13595 (pattern : Twelve) (guard : d1 pattern = 1) : d1303 pattern ≤ (2 : Int) + d1302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13594 pattern childGuard
    simpa only [d1303, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1303, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13596 (pattern : Twelve) (guard : d1 pattern = 1) : d1311 pattern ≤ (2 : Int) + d1310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13572 pattern childGuard
    simpa only [d1311, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13595 pattern childGuard
    simpa only [d1311, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13597 (pattern : Twelve) (guard : d0 pattern = 1) : d1312 pattern ≤ (2 : Int) + d1310 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13598 (pattern : Twelve) (guard : d1844 pattern = 1) : d1317 pattern ≤ (2 : Int) + d1310 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13596 pattern childGuard
    simpa only [d1844, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13597 pattern childGuard
    simpa only [d1844, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13599 (pattern : Twelve) (guard : d1 pattern = 1) : d1310 pattern ≤ (2 : Int) + d1310 pattern := by
  omega
theorem c13600 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d1310 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13601 (pattern : Twelve) (guard : d1844 pattern = 1) : d1318 pattern ≤ (2 : Int) + d1310 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13599 pattern childGuard
    simpa only [d1844, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13600 pattern childGuard
    simpa only [d1844, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13602 (pattern : Twelve) (guard : d1844 pattern = 1) : d1320 pattern ≤ (2 : Int) + d1310 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13598 pattern childGuard
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13601 pattern childGuard
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13603 (pattern : Twelve) (guard : d2270 pattern = 1) : d1322 pattern ≤ (2 : Int) + d1310 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13589 pattern childGuard
    simpa only [d2270, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13602 pattern childGuard
    simpa only [d2270, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13604 (pattern : Twelve) (guard : d2270 pattern = 1) : d1323 pattern ≤ (2 : Int) + d2275 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1323, d2275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13588 pattern childGuard
    simpa only [d1323, d2275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1323, d2275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13603 pattern childGuard
    simpa only [d1323, d2275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13605 (pattern : Twelve) (guard : d0 pattern = 1) : d1660 pattern ≤ (2 : Int) + d1657 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13606 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (2 : Int) + d1644 pattern := by
  omega
theorem c13607 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13515 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13608 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13576 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13607 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13609 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (2 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13454 pattern childGuard
    simpa only [d1644, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13608 pattern childGuard
    simpa only [d1644, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13610 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (2 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13606 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13609 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13611 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (2 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13579 pattern childGuard
    simpa only [d1652, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13610 pattern childGuard
    simpa only [d1652, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13612 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (2 : Int) + d821 pattern := by
  omega
theorem c13613 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13575 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13614 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13607 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13613 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13615 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (2 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13458 pattern childGuard
    simpa only [d821, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13614 pattern childGuard
    simpa only [d821, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13616 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (2 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13612 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13615 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13617 (pattern : Twelve) (guard : d1 pattern = 1) : d1653 pattern ≤ (2 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13616 pattern childGuard
    simpa only [d1653, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1653, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13618 (pattern : Twelve) (guard : d1 pattern = 1) : d1658 pattern ≤ (2 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13611 pattern childGuard
    simpa only [d1658, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13617 pattern childGuard
    simpa only [d1658, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13619 (pattern : Twelve) (guard : d0 pattern = 1) : d1659 pattern ≤ (2 : Int) + d1657 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13620 (pattern : Twelve) (guard : d1844 pattern = 1) : d1661 pattern ≤ (2 : Int) + d1657 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13618 pattern childGuard
    simpa only [d1844, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13619 pattern childGuard
    simpa only [d1844, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13621 (pattern : Twelve) (guard : d1 pattern = 1) : d1657 pattern ≤ (2 : Int) + d1657 pattern := by
  omega
theorem c13622 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d1657 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13623 (pattern : Twelve) (guard : d1844 pattern = 1) : d1662 pattern ≤ (2 : Int) + d1657 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13621 pattern childGuard
    simpa only [d1844, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13622 pattern childGuard
    simpa only [d1844, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13624 (pattern : Twelve) (guard : d1844 pattern = 1) : d1663 pattern ≤ (2 : Int) + d1657 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13620 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13623 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13625 (pattern : Twelve) (guard : d2270 pattern = 1) : d1664 pattern ≤ (2 : Int) + d1657 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13605 pattern childGuard
    simpa only [d2270, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13624 pattern childGuard
    simpa only [d2270, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13626 (pattern : Twelve) (guard : d0 pattern = 1) : d222 pattern ≤ (4 : Int) + d861 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13627 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (4 : Int) + d0 pattern := by
  change (2 : Int) ≤ (4 : Int) + 0
  decide
theorem c13628 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (4 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10458 pattern childGuard
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13627 pattern childGuard
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13629 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (4 : Int) + d1 pattern := by
  change (0 : Int) ≤ (4 : Int) + 1
  decide
theorem c13630 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (4 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10458 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13629 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13631 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (4 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10458 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13630 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13632 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (4 : Int) + d1 pattern := by
  change (2 : Int) ≤ (4 : Int) + 1
  decide
theorem c13633 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (4 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13631 pattern childGuard
    simpa only [d30, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13632 pattern childGuard
    simpa only [d30, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13634 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (4 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13629 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10524 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13635 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (4 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13630 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13634 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13636 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (4 : Int) + d1 pattern := by
  change (3 : Int) ≤ (4 : Int) + 1
  decide
theorem c13637 (pattern : Twelve) (guard : d1 pattern = 1) : d37 pattern ≤ (4 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13635 pattern childGuard
    simpa only [d37, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13636 pattern childGuard
    simpa only [d37, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13638 (pattern : Twelve) (guard : d1 pattern = 1) : d58 pattern ≤ (4 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13633 pattern childGuard
    simpa only [d58, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13637 pattern childGuard
    simpa only [d58, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13639 (pattern : Twelve) (guard : d1 pattern = 1) : d79 pattern ≤ (4 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13628 pattern childGuard
    simpa only [d79, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13638 pattern childGuard
    simpa only [d79, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13640 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (4 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13627 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13632 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13641 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (4 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13627 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13640 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13642 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (4 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13631 pattern childGuard
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13641 pattern childGuard
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13643 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (4 : Int) + d2 pattern := by
  change (0 : Int) ≤ (4 : Int) + 2
  decide
theorem c13644 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (4 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10458 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13643 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13645 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (4 : Int) + d3 pattern := by
  change (1 : Int) ≤ (4 : Int) + 3
  decide
theorem c13646 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (4 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13629 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13645 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13647 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (4 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13644 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13646 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13648 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (4 : Int) + d4 pattern := by
  change (2 : Int) ≤ (4 : Int) + 4
  decide
theorem c13649 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (4 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10461 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13648 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13650 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (4 : Int) + d3 pattern := by
  change (2 : Int) ≤ (4 : Int) + 3
  decide
theorem c13651 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (4 : Int) + d5 pattern := by
  change (3 : Int) ≤ (4 : Int) + 5
  decide
theorem c13652 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (4 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13650 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13651 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13653 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (4 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13649 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13652 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13654 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (4 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13647 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13653 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13655 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (4 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13643 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13648 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13656 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (4 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13645 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13651 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13657 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (4 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13655 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13656 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13658 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (4 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13657 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13659 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (4 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13654 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13658 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13660 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (4 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13642 pattern childGuard
    simpa only [d80, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13659 pattern childGuard
    simpa only [d80, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13661 (pattern : Twelve) (guard : d1 pattern = 1) : d95 pattern ≤ (4 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13639 pattern childGuard
    simpa only [d95, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13660 pattern childGuard
    simpa only [d95, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13662 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (4 : Int) + d2 pattern := by
  change (4 : Int) ≤ (4 : Int) + 2
  decide
theorem c13663 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (4 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13627 pattern childGuard
    simpa only [d38, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13662 pattern childGuard
    simpa only [d38, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13664 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (4 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13627 pattern childGuard
    simpa only [d39, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d39, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13665 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (4 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13663 pattern childGuard
    simpa only [d59, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13664 pattern childGuard
    simpa only [d59, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13666 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (4 : Int) + d3 pattern := by
  change (4 : Int) ≤ (4 : Int) + 3
  decide
theorem c13667 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (4 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13662 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13666 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13668 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (4 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13662 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13667 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13669 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (4 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13641 pattern childGuard
    simpa only [d38, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13668 pattern childGuard
    simpa only [d38, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13670 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (4 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13632 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13636 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13671 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (4 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13640 pattern childGuard
    simpa only [d23, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13670 pattern childGuard
    simpa only [d23, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13672 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (4 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13671 pattern childGuard
    simpa only [d40, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d40, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13673 (pattern : Twelve) (guard : d1 pattern = 1) : d60 pattern ≤ (4 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13669 pattern childGuard
    simpa only [d60, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13672 pattern childGuard
    simpa only [d60, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13674 (pattern : Twelve) (guard : d1 pattern = 1) : d81 pattern ≤ (4 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13665 pattern childGuard
    simpa only [d81, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13673 pattern childGuard
    simpa only [d81, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13675 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (4 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13641 pattern childGuard
    simpa only [d39, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d39, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13676 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (4 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13669 pattern childGuard
    simpa only [d59, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13675 pattern childGuard
    simpa only [d59, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13677 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (4 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13627 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10461 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13678 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (4 : Int) + d3 pattern := by
  omega
theorem c13679 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (4 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13632 pattern childGuard
    simpa only [d9, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13678 pattern childGuard
    simpa only [d9, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13680 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (4 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13677 pattern childGuard
    simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13679 pattern childGuard
    simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13681 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (4 : Int) + d4 pattern := by
  omega
theorem c13682 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (4 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13662 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13681 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13683 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (4 : Int) + d5 pattern := by
  omega
theorem c13684 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (4 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13666 pattern childGuard
    simpa only [d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13683 pattern childGuard
    simpa only [d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13685 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (4 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13682 pattern childGuard
    simpa only [d24, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13684 pattern childGuard
    simpa only [d24, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13686 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (4 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13680 pattern childGuard
    simpa only [d41, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13685 pattern childGuard
    simpa only [d41, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13687 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (4 : Int) + d42 pattern := by
  omega
theorem c13688 (pattern : Twelve) (guard : d1 pattern = 1) : d61 pattern ≤ (4 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13686 pattern childGuard
    simpa only [d61, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13687 pattern childGuard
    simpa only [d61, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13689 (pattern : Twelve) (guard : d1 pattern = 1) : d82 pattern ≤ (4 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13676 pattern childGuard
    simpa only [d82, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13688 pattern childGuard
    simpa only [d82, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13690 (pattern : Twelve) (guard : d1 pattern = 1) : d96 pattern ≤ (4 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13674 pattern childGuard
    simpa only [d96, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13689 pattern childGuard
    simpa only [d96, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13691 (pattern : Twelve) (guard : d1 pattern = 1) : d104 pattern ≤ (4 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13661 pattern childGuard
    simpa only [d104, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13690 pattern childGuard
    simpa only [d104, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13692 (pattern : Twelve) (guard : d0 pattern = 1) : d215 pattern ≤ (4 : Int) + d861 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13693 (pattern : Twelve) (guard : d1835 pattern = 1) : d223 pattern ≤ (4 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13691 pattern childGuard
    simpa only [d1835, d223, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13692 pattern childGuard
    simpa only [d1835, d223, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13694 (pattern : Twelve) (guard : d2266 pattern = 1) : d228 pattern ≤ (4 : Int) + d861 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13626 pattern childGuard
    simpa only [d2266, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13693 pattern childGuard
    simpa only [d2266, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13695 (pattern : Twelve) (guard : d0 pattern = 1) : d224 pattern ≤ (4 : Int) + d864 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13696 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (4 : Int) + d0 pattern := by
  change (1 : Int) ≤ (4 : Int) + 0
  decide
theorem c13697 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (4 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13696 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10524 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13698 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (4 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13697 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10524 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13699 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (4 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13698 pattern childGuard
    simpa only [d46, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13636 pattern childGuard
    simpa only [d46, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13700 (pattern : Twelve) (guard : d1 pattern = 1) : d67 pattern ≤ (4 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13633 pattern childGuard
    simpa only [d67, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13699 pattern childGuard
    simpa only [d67, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13701 (pattern : Twelve) (guard : d1 pattern = 1) : d87 pattern ≤ (4 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13628 pattern childGuard
    simpa only [d87, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13700 pattern childGuard
    simpa only [d87, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13702 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (4 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13631 pattern childGuard
    simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10461 pattern childGuard
    simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13703 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (4 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13641 pattern childGuard
    simpa only [d38, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13662 pattern childGuard
    simpa only [d38, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13704 (pattern : Twelve) (guard : d1 pattern = 1) : d68 pattern ≤ (4 : Int) + d823 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13702 pattern childGuard
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13703 pattern childGuard
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13705 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (4 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13653 pattern childGuard
    simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13706 (pattern : Twelve) (guard : d1 pattern = 1) : d64 pattern ≤ (4 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13654 pattern childGuard
    simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13705 pattern childGuard
    simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13707 (pattern : Twelve) (guard : d1 pattern = 1) : d88 pattern ≤ (4 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13704 pattern childGuard
    simpa only [d88, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13706 pattern childGuard
    simpa only [d88, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13708 (pattern : Twelve) (guard : d1 pattern = 1) : d100 pattern ≤ (4 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13701 pattern childGuard
    simpa only [d100, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13707 pattern childGuard
    simpa only [d100, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13709 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (4 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13636 pattern childGuard
    simpa only [d47, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d47, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13710 (pattern : Twelve) (guard : d1 pattern = 1) : d69 pattern ≤ (4 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13669 pattern childGuard
    simpa only [d69, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13709 pattern childGuard
    simpa only [d69, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13711 (pattern : Twelve) (guard : d1 pattern = 1) : d89 pattern ≤ (4 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13665 pattern childGuard
    simpa only [d89, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13710 pattern childGuard
    simpa only [d89, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13712 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (4 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13662 pattern childGuard
    simpa only [d48, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d48, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13713 (pattern : Twelve) (guard : d1 pattern = 1) : d70 pattern ≤ (4 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13669 pattern childGuard
    simpa only [d70, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13712 pattern childGuard
    simpa only [d70, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13714 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (4 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13685 pattern childGuard
    simpa only [d49, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d49, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13715 (pattern : Twelve) (guard : d1 pattern = 1) : d71 pattern ≤ (4 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13686 pattern childGuard
    simpa only [d71, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13714 pattern childGuard
    simpa only [d71, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13716 (pattern : Twelve) (guard : d1 pattern = 1) : d90 pattern ≤ (4 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13713 pattern childGuard
    simpa only [d90, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13715 pattern childGuard
    simpa only [d90, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13717 (pattern : Twelve) (guard : d1 pattern = 1) : d101 pattern ≤ (4 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13711 pattern childGuard
    simpa only [d101, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13716 pattern childGuard
    simpa only [d101, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13718 (pattern : Twelve) (guard : d1 pattern = 1) : d108 pattern ≤ (4 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13708 pattern childGuard
    simpa only [d108, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13717 pattern childGuard
    simpa only [d108, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13719 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (4 : Int) + d864 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban21.Diagram
