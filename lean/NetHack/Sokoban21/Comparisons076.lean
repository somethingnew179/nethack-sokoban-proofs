/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons075
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c10640 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (4 : Int) + d1644 pattern := by
  omega
theorem c10641 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (4 : Int) + d1324 pattern := by
  omega
theorem c10642 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (4 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10641 pattern childGuard
    simpa only [d1644, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10477 pattern childGuard
    simpa only [d1644, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10643 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (4 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10640 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10642 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10644 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (4 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10609 pattern childGuard
    simpa only [d1652, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10643 pattern childGuard
    simpa only [d1652, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10645 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (4 : Int) + d821 pattern := by
  omega
theorem c10646 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (4 : Int) + d25 pattern := by
  omega
theorem c10647 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (4 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10646 pattern childGuard
    simpa only [d821, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10481 pattern childGuard
    simpa only [d821, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10648 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (4 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10645 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10647 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10649 (pattern : Twelve) (guard : d1 pattern = 1) : d1653 pattern ≤ (4 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10648 pattern childGuard
    simpa only [d1653, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d1653, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10650 (pattern : Twelve) (guard : d1 pattern = 1) : d1658 pattern ≤ (4 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10644 pattern childGuard
    simpa only [d1658, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10649 pattern childGuard
    simpa only [d1658, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10651 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10477 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10485 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10652 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10477 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10653 (pattern : Twelve) (guard : d1 pattern = 1) : d1648 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10651 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10652 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10654 (pattern : Twelve) (guard : d1 pattern = 1) : d1654 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10618 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10653 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10655 (pattern : Twelve) (guard : d1 pattern = 1) : d1655 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10574 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10656 (pattern : Twelve) (guard : d1 pattern = 1) : d1659 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10654 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10655 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10657 (pattern : Twelve) (guard : d1 pattern = 1) : d1661 pattern ≤ (4 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10650 pattern childGuard
    simpa only [d1661, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10656 pattern childGuard
    simpa only [d1661, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10658 (pattern : Twelve) (guard : d0 pattern = 1) : d1662 pattern ≤ (4 : Int) + d1662 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10659 (pattern : Twelve) (guard : d1835 pattern = 1) : d1663 pattern ≤ (4 : Int) + d1662 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10657 pattern childGuard
    simpa only [d1835, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10658 pattern childGuard
    simpa only [d1835, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10660 (pattern : Twelve) (guard : d1835 pattern = 1) : d1664 pattern ≤ (4 : Int) + d1889 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1664, d1889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10639 pattern childGuard
    simpa only [d1664, d1889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1664, d1889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10659 pattern childGuard
    simpa only [d1664, d1889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10661 (pattern : Twelve) (guard : d0 pattern = 1) : d102 pattern ≤ (3 : Int) + d861 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10662 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (3 : Int) + d0 pattern := by
  omega
theorem c10663 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (3 : Int) + d1 pattern := by
  change (0 : Int) ≤ (3 : Int) + 1
  decide
theorem c10664 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (3 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10662 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10663 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10665 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (3 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10662 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10664 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10666 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (3 : Int) + d1 pattern := by
  omega
theorem c10667 (pattern : Twelve) (guard : d1 pattern = 1) : d26 pattern ≤ (3 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10665 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10666 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10668 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (3 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10663 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10666 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10669 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (3 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10664 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10668 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10670 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (3 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10669 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10666 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10671 (pattern : Twelve) (guard : d1 pattern = 1) : d50 pattern ≤ (3 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10667 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10670 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10672 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (3 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10662 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10671 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10673 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (3 : Int) + d2 pattern := by
  change (0 : Int) ≤ (3 : Int) + 2
  decide
theorem c10674 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (3 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10662 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10673 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10675 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (3 : Int) + d3 pattern := by
  change (1 : Int) ≤ (3 : Int) + 3
  decide
theorem c10676 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (3 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10663 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10675 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10677 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (3 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10674 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10676 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10678 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (3 : Int) + d2 pattern := by
  omega
theorem c10679 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (3 : Int) + d4 pattern := by
  change (2 : Int) ≤ (3 : Int) + 4
  decide
theorem c10680 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (3 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10678 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10679 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10681 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (3 : Int) + d3 pattern := by
  change (2 : Int) ≤ (3 : Int) + 3
  decide
theorem c10682 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (3 : Int) + d5 pattern := by
  change (3 : Int) ≤ (3 : Int) + 5
  decide
theorem c10683 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (3 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10681 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10682 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10684 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (3 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10680 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10683 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10685 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (3 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10677 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10684 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10686 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (3 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10673 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10679 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10687 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (3 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10675 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10682 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10688 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (3 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10686 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10687 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10689 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (3 : Int) + d6 pattern := by
  omega
theorem c10690 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (3 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10688 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10691 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (3 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10685 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10690 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10692 (pattern : Twelve) (guard : d1 pattern = 1) : d76 pattern ≤ (3 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10665 pattern childGuard
    simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10691 pattern childGuard
    simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10693 (pattern : Twelve) (guard : d1 pattern = 1) : d93 pattern ≤ (3 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10672 pattern childGuard
    simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10692 pattern childGuard
    simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10694 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (3 : Int) + d56 pattern := by
  omega
theorem c10695 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (3 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10678 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10681 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10696 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (3 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10678 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10695 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10697 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (3 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10665 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10696 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10698 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (3 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10669 pattern childGuard
    simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10699 (pattern : Twelve) (guard : d1 pattern = 1) : d57 pattern ≤ (3 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10697 pattern childGuard
    simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10698 pattern childGuard
    simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10700 (pattern : Twelve) (guard : d1 pattern = 1) : d77 pattern ≤ (3 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10694 pattern childGuard
    simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10699 pattern childGuard
    simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10701 (pattern : Twelve) (guard : d1 pattern = 1) : d35 pattern ≤ (3 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10665 pattern childGuard
    simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10702 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (3 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10697 pattern childGuard
    simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10701 pattern childGuard
    simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10703 (pattern : Twelve) (guard : d1 pattern = 1) : d78 pattern ≤ (3 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10702 pattern childGuard
    simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10691 pattern childGuard
    simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10704 (pattern : Twelve) (guard : d1 pattern = 1) : d94 pattern ≤ (3 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10700 pattern childGuard
    simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10703 pattern childGuard
    simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10705 (pattern : Twelve) (guard : d1 pattern = 1) : d103 pattern ≤ (3 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10693 pattern childGuard
    simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10704 pattern childGuard
    simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10706 (pattern : Twelve) (guard : d1836 pattern = 1) : d110 pattern ≤ (3 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1836, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10661 pattern childGuard
    simpa only [d1836, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1836, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10705 pattern childGuard
    simpa only [d1836, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10707 (pattern : Twelve) (guard : d0 pattern = 1) : d217 pattern ≤ (3 : Int) + d862 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10708 (pattern : Twelve) (guard : d1890 pattern = 1) : d345 pattern ≤ (3 : Int) + d1891 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d345, d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10706 pattern childGuard
    simpa only [d1890, d345, d1891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d345, d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10707 pattern childGuard
    simpa only [d1890, d345, d1891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10709 (pattern : Twelve) (guard : d0 pattern = 1) : d106 pattern ≤ (3 : Int) + d864 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10710 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (3 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10665 pattern childGuard
    simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10678 pattern childGuard
    simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10711 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (3 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10710 pattern childGuard
    simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10691 pattern childGuard
    simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10712 (pattern : Twelve) (guard : d1 pattern = 1) : d97 pattern ≤ (3 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10672 pattern childGuard
    simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10711 pattern childGuard
    simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10713 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (3 : Int) + d45 pattern := by
  omega
theorem c10714 (pattern : Twelve) (guard : d1 pattern = 1) : d65 pattern ≤ (3 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10697 pattern childGuard
    simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10713 pattern childGuard
    simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10715 (pattern : Twelve) (guard : d1 pattern = 1) : d85 pattern ≤ (3 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10694 pattern childGuard
    simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10714 pattern childGuard
    simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10716 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (3 : Int) + d39 pattern := by
  omega
theorem c10717 (pattern : Twelve) (guard : d1 pattern = 1) : d66 pattern ≤ (3 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10697 pattern childGuard
    simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10716 pattern childGuard
    simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10718 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (3 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10684 pattern childGuard
    simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10719 (pattern : Twelve) (guard : d1 pattern = 1) : d64 pattern ≤ (3 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10685 pattern childGuard
    simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10718 pattern childGuard
    simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10720 (pattern : Twelve) (guard : d1 pattern = 1) : d86 pattern ≤ (3 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10717 pattern childGuard
    simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10719 pattern childGuard
    simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10721 (pattern : Twelve) (guard : d1 pattern = 1) : d99 pattern ≤ (3 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10715 pattern childGuard
    simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10720 pattern childGuard
    simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10722 (pattern : Twelve) (guard : d1 pattern = 1) : d107 pattern ≤ (3 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10712 pattern childGuard
    simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10721 pattern childGuard
    simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10723 (pattern : Twelve) (guard : d1836 pattern = 1) : d112 pattern ≤ (3 : Int) + d864 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1836, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10709 pattern childGuard
    simpa only [d1836, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1836, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10722 pattern childGuard
    simpa only [d1836, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10724 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (3 : Int) + d865 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10725 (pattern : Twelve) (guard : d1890 pattern = 1) : d346 pattern ≤ (3 : Int) + d1892 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d346, d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10723 pattern childGuard
    simpa only [d1890, d346, d1892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d346, d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10724 pattern childGuard
    simpa only [d1890, d346, d1892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10726 (pattern : Twelve) (guard : d1890 pattern = 1) : d348 pattern ≤ (3 : Int) + d1893 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1890 pattern = 1 := by simpa only [d348, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10708 pattern childGuard
    simpa only [d348, d1893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1890 pattern = 1 := by simpa only [d348, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10725 pattern childGuard
    simpa only [d348, d1893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10727 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (3 : Int) + d862 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10728 (pattern : Twelve) (guard : d1890 pattern = 1) : d347 pattern ≤ (3 : Int) + d1891 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d347, d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10706 pattern childGuard
    simpa only [d1890, d347, d1891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d347, d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10727 pattern childGuard
    simpa only [d1890, d347, d1891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10729 (pattern : Twelve) (guard : d1890 pattern = 1) : d349 pattern ≤ (3 : Int) + d1893 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1890 pattern = 1 := by simpa only [d349, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10728 pattern childGuard
    simpa only [d349, d1893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1890 pattern = 1 := by simpa only [d349, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10725 pattern childGuard
    simpa only [d349, d1893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10730 (pattern : Twelve) (guard : d1890 pattern = 1) : d350 pattern ≤ (3 : Int) + d1893 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1890 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10726 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1890 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10729 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10731 (pattern : Twelve) (guard : d1890 pattern = 1) : d351 pattern ≤ (3 : Int) + d1893 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1890 pattern = 1 := by simpa only [d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10730 pattern childGuard
    simpa only [d351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1890 pattern = 1 := by simpa only [d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10729 pattern childGuard
    simpa only [d351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10732 (pattern : Twelve) (guard : d0 pattern = 1) : d861 pattern ≤ (3 : Int) + d1313 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10733 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (3 : Int) + d2 pattern := by
  change (1 : Int) ≤ (3 : Int) + 2
  decide
theorem c10734 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (3 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10663 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10733 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10735 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (3 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10664 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10734 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10736 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (3 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10666 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10733 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10737 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (3 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10666 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10736 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10738 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (3 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10735 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10737 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10739 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (3 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10668 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10736 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10740 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (3 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10739 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10737 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10741 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (3 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10738 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10740 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10742 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (3 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10665 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10741 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10743 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (3 : Int) + d6 pattern := by
  change (0 : Int) ≤ (3 : Int) + 6
  decide
theorem c10744 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (3 : Int) + d6 pattern := by
  change (2 : Int) ≤ (3 : Int) + 6
  decide
theorem c10745 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10743 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10744 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10746 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (3 : Int) + d6 pattern := by
  change (1 : Int) ≤ (3 : Int) + 6
  decide
theorem c10747 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (3 : Int) + d6 pattern := by
  change (3 : Int) ≤ (3 : Int) + 6
  decide
theorem c10748 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10746 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10747 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10749 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10745 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10748 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10750 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (3 : Int) + d6 pattern := by
  change (4 : Int) ≤ (3 : Int) + 6
  decide
theorem c10751 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10744 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10750 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10752 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (3 : Int) + d6 pattern := by
  change (5 : Int) ≤ (3 : Int) + 6
  decide
theorem c10753 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10747 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10752 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10754 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10751 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10753 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10755 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10749 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10754 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10756 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10754 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10757 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10755 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10756 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10758 (pattern : Twelve) (guard : d1 pattern = 1) : d839 pattern ≤ (3 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10677 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10757 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10759 (pattern : Twelve) (guard : d1 pattern = 1) : d853 pattern ≤ (3 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10742 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10758 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10760 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (3 : Int) + d4 pattern := by
  change (3 : Int) ≤ (3 : Int) + 4
  decide
theorem c10761 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (3 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10681 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10760 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10762 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (3 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10695 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10761 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10763 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (3 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10735 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10762 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10764 (pattern : Twelve) (guard : d1 pattern = 1) : d818 pattern ≤ (3 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10739 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10765 (pattern : Twelve) (guard : d1 pattern = 1) : d826 pattern ≤ (3 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10763 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10764 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10766 (pattern : Twelve) (guard : d1 pattern = 1) : d840 pattern ≤ (3 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10702 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10765 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10767 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (3 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10677 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10768 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (3 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10685 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10767 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10769 (pattern : Twelve) (guard : d1 pattern = 1) : d841 pattern ≤ (3 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10768 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10757 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10770 (pattern : Twelve) (guard : d1 pattern = 1) : d854 pattern ≤ (3 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10766 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10769 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10771 (pattern : Twelve) (guard : d1 pattern = 1) : d861 pattern ≤ (3 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10759 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10770 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10772 (pattern : Twelve) (guard : d1836 pattern = 1) : d861 pattern ≤ (3 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10732 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10771 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10773 (pattern : Twelve) (guard : d0 pattern = 1) : d922 pattern ≤ (3 : Int) + d1314 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10774 (pattern : Twelve) (guard : d1890 pattern = 1) : d1011 pattern ≤ (3 : Int) + d1894 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d1011, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10772 pattern childGuard
    simpa only [d1890, d1011, d1894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d1011, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10773 pattern childGuard
    simpa only [d1890, d1011, d1894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10775 (pattern : Twelve) (guard : d0 pattern = 1) : d864 pattern ≤ (3 : Int) + d1316 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10776 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (3 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10677 pattern childGuard
    simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10696 pattern childGuard
    simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10777 (pattern : Twelve) (guard : d1 pattern = 1) : d846 pattern ≤ (3 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10776 pattern childGuard
    simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10757 pattern childGuard
    simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10778 (pattern : Twelve) (guard : d1 pattern = 1) : d857 pattern ≤ (3 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10742 pattern childGuard
    simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10777 pattern childGuard
    simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10779 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (3 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10737 pattern childGuard
    simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
