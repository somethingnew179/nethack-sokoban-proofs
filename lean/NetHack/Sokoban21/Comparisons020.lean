/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons019
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c2800 (pattern : Twelve) (guard : d1864 pattern = 1) : d1706 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1706, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2799 pattern childGuard
    simpa only [d1864, d1706, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1706, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2773 pattern childGuard
    simpa only [d1864, d1706, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2801 (pattern : Twelve) (guard : d1864 pattern = 1) : d1709 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2794 pattern childGuard
    simpa only [d1709, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2800 pattern childGuard
    simpa only [d1709, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2802 (pattern : Twelve) (guard : d0 pattern = 1) : d1644 pattern ≤ (0 : Int) + d1645 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2803 (pattern : Twelve) (guard : d1849 pattern = 1) : d1644 pattern ≤ (0 : Int) + d1645 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1531 pattern childGuard
    simpa only [d1849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2802 pattern childGuard
    simpa only [d1849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2804 (pattern : Twelve) (guard : d1863 pattern = 1) : d1652 pattern ≤ (0 : Int) + d1716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1652, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1405 pattern childGuard
    simpa only [d1863, d1652, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1652, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2803 pattern childGuard
    simpa only [d1863, d1652, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2805 (pattern : Twelve) (guard : d1864 pattern = 1) : d1707 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1707, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2804 pattern childGuard
    simpa only [d1864, d1707, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1707, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2773 pattern childGuard
    simpa only [d1864, d1707, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2806 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (0 : Int) + d42 pattern := by
  omega
theorem c2807 (pattern : Twelve) (guard : d1848 pattern = 1) : d1289 pattern ≤ (0 : Int) + d42 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1432 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2806 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2808 (pattern : Twelve) (guard : d0 pattern = 1) : d128 pattern ≤ (0 : Int) + d128 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2809 (pattern : Twelve) (guard : d1849 pattern = 1) : d1648 pattern ≤ (0 : Int) + d128 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1538 pattern childGuard
    simpa only [d1849, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2808 pattern childGuard
    simpa only [d1849, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2810 (pattern : Twelve) (guard : d1863 pattern = 1) : d1654 pattern ≤ (0 : Int) + d1717 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1654, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2807 pattern childGuard
    simpa only [d1863, d1654, d1717, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1654, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2809 pattern childGuard
    simpa only [d1863, d1654, d1717, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2811 (pattern : Twelve) (guard : d1864 pattern = 1) : d1708 pattern ≤ (0 : Int) + d1720 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1708, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2810 pattern childGuard
    simpa only [d1864, d1708, d1720, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1708, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2170 pattern childGuard
    simpa only [d1864, d1708, d1720, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2812 (pattern : Twelve) (guard : d1864 pattern = 1) : d1710 pattern ≤ (0 : Int) + d1722 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1710, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2805 pattern childGuard
    simpa only [d1710, d1722, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1710, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2811 pattern childGuard
    simpa only [d1710, d1722, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2813 (pattern : Twelve) (guard : d1864 pattern = 1) : d1711 pattern ≤ (0 : Int) + d1723 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1711, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2800 pattern childGuard
    simpa only [d1711, d1723, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1711, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2593 pattern childGuard
    simpa only [d1711, d1723, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2814 (pattern : Twelve) (guard : d1864 pattern = 1) : d1712 pattern ≤ (0 : Int) + d1725 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1712, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2812 pattern childGuard
    simpa only [d1712, d1725, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1712, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2813 pattern childGuard
    simpa only [d1712, d1725, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2815 (pattern : Twelve) (guard : d1864 pattern = 1) : d1713 pattern ≤ (0 : Int) + d1727 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1713, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2801 pattern childGuard
    simpa only [d1713, d1727, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1713, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2814 pattern childGuard
    simpa only [d1713, d1727, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2816 (pattern : Twelve) (guard : d0 pattern = 1) : d128 pattern ≤ (0 : Int) + d183 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2817 (pattern : Twelve) (guard : d1849 pattern = 1) : d1648 pattern ≤ (0 : Int) + d1667 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1648, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1538 pattern childGuard
    simpa only [d1849, d1648, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1648, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2816 pattern childGuard
    simpa only [d1849, d1648, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2818 (pattern : Twelve) (guard : d1863 pattern = 1) : d1654 pattern ≤ (0 : Int) + d1718 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1654, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2807 pattern childGuard
    simpa only [d1863, d1654, d1718, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1654, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2817 pattern childGuard
    simpa only [d1863, d1654, d1718, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2819 (pattern : Twelve) (guard : d1864 pattern = 1) : d1708 pattern ≤ (0 : Int) + d1721 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1708, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2818 pattern childGuard
    simpa only [d1864, d1708, d1721, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1708, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2411 pattern childGuard
    simpa only [d1864, d1708, d1721, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2820 (pattern : Twelve) (guard : d1864 pattern = 1) : d1710 pattern ≤ (0 : Int) + d1724 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1710, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2805 pattern childGuard
    simpa only [d1710, d1724, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1710, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2819 pattern childGuard
    simpa only [d1710, d1724, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2821 (pattern : Twelve) (guard : d1864 pattern = 1) : d1712 pattern ≤ (0 : Int) + d1726 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1712, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2820 pattern childGuard
    simpa only [d1712, d1726, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1712, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2813 pattern childGuard
    simpa only [d1712, d1726, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2822 (pattern : Twelve) (guard : d1864 pattern = 1) : d1713 pattern ≤ (0 : Int) + d1728 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1713, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2801 pattern childGuard
    simpa only [d1713, d1728, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1713, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2821 pattern childGuard
    simpa only [d1713, d1728, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2823 (pattern : Twelve) (guard : d1864 pattern = 1) : d1713 pattern ≤ (0 : Int) + d1729 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2815 pattern childGuard
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2822 pattern childGuard
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2824 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c2825 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d477 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1262 pattern childGuard
    simpa only [d1865, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2826 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d498 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2824 pattern childGuard
    simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2825 pattern childGuard
    simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2827 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d157 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2828 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d478 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d478, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2827 pattern childGuard
    simpa only [d1865, d478, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2829 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d499 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2824 pattern childGuard
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2828 pattern childGuard
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2830 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d532 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2826 pattern childGuard
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2829 pattern childGuard
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2831 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (0 : Int) + d1 pattern := by
  omega
theorem c2832 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d157 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2833 (pattern : Twelve) (guard : d1865 pattern = 1) : d1 pattern ≤ (0 : Int) + d161 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d1865, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2832 pattern childGuard
    simpa only [d1865, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2834 (pattern : Twelve) (guard : d1865 pattern = 1) : d26 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d26, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2824 pattern childGuard
    simpa only [d26, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d26, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2833 pattern childGuard
    simpa only [d26, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2835 (pattern : Twelve) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d158 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2836 (pattern : Twelve) (guard : d1865 pattern = 1) : d17 pattern ≤ (0 : Int) + d162 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d17, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d17, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d17, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2835 pattern childGuard
    simpa only [d1865, d17, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2837 (pattern : Twelve) (guard : d1865 pattern = 1) : d1 pattern ≤ (0 : Int) + d479 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d1865, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1356 pattern childGuard
    simpa only [d1865, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2838 (pattern : Twelve) (guard : d1865 pattern = 1) : d27 pattern ≤ (0 : Int) + d500 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d27, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2836 pattern childGuard
    simpa only [d27, d500, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d27, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2837 pattern childGuard
    simpa only [d27, d500, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2839 (pattern : Twelve) (guard : d1865 pattern = 1) : d50 pattern ≤ (0 : Int) + d533 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d50, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2834 pattern childGuard
    simpa only [d50, d533, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d50, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2838 pattern childGuard
    simpa only [d50, d533, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2840 (pattern : Twelve) (guard : d1865 pattern = 1) : d72 pattern ≤ (0 : Int) + d561 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d72, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2830 pattern childGuard
    simpa only [d72, d561, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d72, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2839 pattern childGuard
    simpa only [d72, d561, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2841 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d158 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2842 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d162 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2841 pattern childGuard
    simpa only [d1865, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2843 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d480 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c157 pattern childGuard
    simpa only [d1865, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2844 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d501 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2842 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2845 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d534 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2829 pattern childGuard
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2844 pattern childGuard
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2846 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (0 : Int) + d8 pattern := by
  omega
theorem c2847 (pattern : Twelve) (guard : d0 pattern = 1) : d9 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2848 (pattern : Twelve) (guard : d1865 pattern = 1) : d18 pattern ≤ (0 : Int) + d481 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d18, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2846 pattern childGuard
    simpa only [d1865, d18, d481, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d18, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2847 pattern childGuard
    simpa only [d1865, d18, d481, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2849 (pattern : Twelve) (guard : d1865 pattern = 1) : d28 pattern ≤ (0 : Int) + d502 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d28, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2836 pattern childGuard
    simpa only [d28, d502, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d28, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2848 pattern childGuard
    simpa only [d28, d502, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2850 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c2851 (pattern : Twelve) (guard : d0 pattern = 1) : d11 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2852 (pattern : Twelve) (guard : d1865 pattern = 1) : d19 pattern ≤ (0 : Int) + d482 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d19, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2850 pattern childGuard
    simpa only [d1865, d19, d482, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d19, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2851 pattern childGuard
    simpa only [d1865, d19, d482, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2853 (pattern : Twelve) (guard : d1865 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c2854 (pattern : Twelve) (guard : d1865 pattern = 1) : d29 pattern ≤ (0 : Int) + d503 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d29, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2852 pattern childGuard
    simpa only [d29, d503, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d29, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d29, d503, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2855 (pattern : Twelve) (guard : d1865 pattern = 1) : d51 pattern ≤ (0 : Int) + d535 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d51, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2849 pattern childGuard
    simpa only [d51, d535, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d51, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2854 pattern childGuard
    simpa only [d51, d535, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2856 (pattern : Twelve) (guard : d1865 pattern = 1) : d73 pattern ≤ (0 : Int) + d562 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d73, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2845 pattern childGuard
    simpa only [d73, d562, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d73, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2855 pattern childGuard
    simpa only [d73, d562, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2857 (pattern : Twelve) (guard : d1865 pattern = 1) : d91 pattern ≤ (0 : Int) + d588 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d91, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2840 pattern childGuard
    simpa only [d91, d588, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d91, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2856 pattern childGuard
    simpa only [d91, d588, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2858 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2859 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d483 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d483, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2858 pattern childGuard
    simpa only [d1865, d483, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2860 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d159 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2861 (pattern : Twelve) (guard : d1865 pattern = 1) : d2 pattern ≤ (0 : Int) + d484 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1865, d484, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2860 pattern childGuard
    simpa only [d1865, d484, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2862 (pattern : Twelve) (guard : d1865 pattern = 1) : d30 pattern ≤ (0 : Int) + d504 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d30, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2859 pattern childGuard
    simpa only [d30, d504, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d30, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2861 pattern childGuard
    simpa only [d30, d504, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2863 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d160 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2864 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d485 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d485, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2863 pattern childGuard
    simpa only [d1865, d485, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2865 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (0 : Int) + d12 pattern := by
  omega
theorem c2866 (pattern : Twelve) (guard : d0 pattern = 1) : d13 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2867 (pattern : Twelve) (guard : d1865 pattern = 1) : d20 pattern ≤ (0 : Int) + d486 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d20, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2865 pattern childGuard
    simpa only [d1865, d20, d486, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d20, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2866 pattern childGuard
    simpa only [d1865, d20, d486, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2868 (pattern : Twelve) (guard : d1865 pattern = 1) : d31 pattern ≤ (0 : Int) + d505 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d31, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2864 pattern childGuard
    simpa only [d31, d505, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d31, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2867 pattern childGuard
    simpa only [d31, d505, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2869 (pattern : Twelve) (guard : d1865 pattern = 1) : d52 pattern ≤ (0 : Int) + d536 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d52, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2862 pattern childGuard
    simpa only [d52, d536, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d52, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2868 pattern childGuard
    simpa only [d52, d536, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2870 (pattern : Twelve) (guard : d1865 pattern = 1) : d2 pattern ≤ (0 : Int) + d487 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1865, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1311 pattern childGuard
    simpa only [d1865, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2871 (pattern : Twelve) (guard : d1865 pattern = 1) : d30 pattern ≤ (0 : Int) + d506 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d30, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2864 pattern childGuard
    simpa only [d30, d506, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d30, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2870 pattern childGuard
    simpa only [d30, d506, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2872 (pattern : Twelve) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2873 (pattern : Twelve) (guard : d1865 pattern = 1) : d17 pattern ≤ (0 : Int) + d480 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d17, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d17, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d17, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2872 pattern childGuard
    simpa only [d1865, d17, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2874 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (0 : Int) + d13 pattern := by
  omega
theorem c2875 (pattern : Twelve) (guard : d0 pattern = 1) : d14 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2876 (pattern : Twelve) (guard : d1865 pattern = 1) : d21 pattern ≤ (0 : Int) + d170 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d21, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2874 pattern childGuard
    simpa only [d1865, d21, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d21, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2875 pattern childGuard
    simpa only [d1865, d21, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2877 (pattern : Twelve) (guard : d1865 pattern = 1) : d32 pattern ≤ (0 : Int) + d507 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d32, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d32, d507, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d32, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2876 pattern childGuard
    simpa only [d32, d507, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2878 (pattern : Twelve) (guard : d1865 pattern = 1) : d53 pattern ≤ (0 : Int) + d537 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d53, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2871 pattern childGuard
    simpa only [d53, d537, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d53, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2877 pattern childGuard
    simpa only [d53, d537, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2879 (pattern : Twelve) (guard : d1865 pattern = 1) : d74 pattern ≤ (0 : Int) + d563 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d74, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2869 pattern childGuard
    simpa only [d74, d563, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d74, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2878 pattern childGuard
    simpa only [d74, d563, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2880 (pattern : Twelve) (guard : d1865 pattern = 1) : d22 pattern ≤ (0 : Int) + d22 pattern := by
  omega
theorem c2881 (pattern : Twelve) (guard : d1865 pattern = 1) : d33 pattern ≤ (0 : Int) + d508 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d33, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d33, d508, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d33, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2880 pattern childGuard
    simpa only [d33, d508, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2882 (pattern : Twelve) (guard : d1865 pattern = 1) : d54 pattern ≤ (0 : Int) + d538 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d54, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2871 pattern childGuard
    simpa only [d54, d538, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d54, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2881 pattern childGuard
    simpa only [d54, d538, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2883 (pattern : Twelve) (guard : d1865 pattern = 1) : d23 pattern ≤ (0 : Int) + d487 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d23, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1865, d23, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d23, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2847 pattern childGuard
    simpa only [d1865, d23, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2884 (pattern : Twelve) (guard : d1865 pattern = 1) : d34 pattern ≤ (0 : Int) + d509 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d34, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d34, d509, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d34, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2883 pattern childGuard
    simpa only [d34, d509, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2885 (pattern : Twelve) (guard : d1865 pattern = 1) : d55 pattern ≤ (0 : Int) + d539 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d55, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2884 pattern childGuard
    simpa only [d55, d539, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d55, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2854 pattern childGuard
    simpa only [d55, d539, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2886 (pattern : Twelve) (guard : d1865 pattern = 1) : d75 pattern ≤ (0 : Int) + d564 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d75, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2882 pattern childGuard
    simpa only [d75, d564, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d75, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2885 pattern childGuard
    simpa only [d75, d564, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2887 (pattern : Twelve) (guard : d1865 pattern = 1) : d92 pattern ≤ (0 : Int) + d589 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d92, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2879 pattern childGuard
    simpa only [d92, d589, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d92, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2886 pattern childGuard
    simpa only [d92, d589, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2888 (pattern : Twelve) (guard : d1865 pattern = 1) : d102 pattern ≤ (0 : Int) + d606 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d102, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2857 pattern childGuard
    simpa only [d102, d606, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d102, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2887 pattern childGuard
    simpa only [d102, d606, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2889 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d159 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2890 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d488 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d488, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2889 pattern childGuard
    simpa only [d1865, d488, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2891 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d510 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2859 pattern childGuard
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2890 pattern childGuard
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2892 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d511 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2864 pattern childGuard
    simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2893 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d540 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2891 pattern childGuard
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2892 pattern childGuard
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2894 (pattern : Twelve) (guard : d1865 pattern = 1) : d26 pattern ≤ (0 : Int) + d512 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d26, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2864 pattern childGuard
    simpa only [d26, d512, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d26, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2837 pattern childGuard
    simpa only [d26, d512, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2895 (pattern : Twelve) (guard : d1865 pattern = 1) : d27 pattern ≤ (0 : Int) + d513 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d27, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d27, d513, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d27, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2837 pattern childGuard
    simpa only [d27, d513, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2896 (pattern : Twelve) (guard : d1865 pattern = 1) : d50 pattern ≤ (0 : Int) + d541 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d50, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2894 pattern childGuard
    simpa only [d50, d541, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d50, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2895 pattern childGuard
    simpa only [d50, d541, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2897 (pattern : Twelve) (guard : d1865 pattern = 1) : d72 pattern ≤ (0 : Int) + d565 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d72, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2893 pattern childGuard
    simpa only [d72, d565, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d72, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2896 pattern childGuard
    simpa only [d72, d565, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2898 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d542 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2892 pattern childGuard
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2899 (pattern : Twelve) (guard : d1865 pattern = 1) : d76 pattern ≤ (0 : Int) + d566 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d76, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2898 pattern childGuard
    simpa only [d76, d566, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d76, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2885 pattern childGuard
    simpa only [d76, d566, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2900 (pattern : Twelve) (guard : d1865 pattern = 1) : d93 pattern ≤ (0 : Int) + d590 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d93, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2897 pattern childGuard
    simpa only [d93, d590, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d93, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2899 pattern childGuard
    simpa only [d93, d590, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2901 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d13 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2902 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d489 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d489, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2901 pattern childGuard
    simpa only [d1865, d489, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2903 (pattern : Twelve) (guard : d1865 pattern = 1) : d30 pattern ≤ (0 : Int) + d514 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d30, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2902 pattern childGuard
    simpa only [d30, d514, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d30, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2870 pattern childGuard
    simpa only [d30, d514, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2904 (pattern : Twelve) (guard : d1865 pattern = 1) : d35 pattern ≤ (0 : Int) + d515 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d35, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d35, d515, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d35, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d35, d515, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2905 (pattern : Twelve) (guard : d1865 pattern = 1) : d56 pattern ≤ (0 : Int) + d543 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d56, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2903 pattern childGuard
    simpa only [d56, d543, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d56, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2904 pattern childGuard
    simpa only [d56, d543, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2906 (pattern : Twelve) (guard : d1865 pattern = 1) : d30 pattern ≤ (0 : Int) + d509 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d30, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d30, d509, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d30, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2870 pattern childGuard
    simpa only [d30, d509, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2907 (pattern : Twelve) (guard : d1865 pattern = 1) : d36 pattern ≤ (0 : Int) + d515 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d36, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d36, d515, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d36, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d36, d515, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2908 (pattern : Twelve) (guard : d1865 pattern = 1) : d57 pattern ≤ (0 : Int) + d544 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d57, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2906 pattern childGuard
    simpa only [d57, d544, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d57, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2907 pattern childGuard
    simpa only [d57, d544, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2909 (pattern : Twelve) (guard : d1865 pattern = 1) : d77 pattern ≤ (0 : Int) + d567 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d77, d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2905 pattern childGuard
    simpa only [d77, d567, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d77, d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2908 pattern childGuard
    simpa only [d77, d567, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2910 (pattern : Twelve) (guard : d1865 pattern = 1) : d56 pattern ≤ (0 : Int) + d544 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d56, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2906 pattern childGuard
    simpa only [d56, d544, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d56, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2904 pattern childGuard
    simpa only [d56, d544, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2911 (pattern : Twelve) (guard : d1865 pattern = 1) : d78 pattern ≤ (0 : Int) + d568 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d78, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2910 pattern childGuard
    simpa only [d78, d568, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d78, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2885 pattern childGuard
    simpa only [d78, d568, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2912 (pattern : Twelve) (guard : d1865 pattern = 1) : d94 pattern ≤ (0 : Int) + d591 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d94, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2909 pattern childGuard
    simpa only [d94, d591, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d94, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2911 pattern childGuard
    simpa only [d94, d591, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2913 (pattern : Twelve) (guard : d1865 pattern = 1) : d103 pattern ≤ (0 : Int) + d607 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d103, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2900 pattern childGuard
    simpa only [d103, d607, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d103, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2912 pattern childGuard
    simpa only [d103, d607, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2914 (pattern : Twelve) (guard : d1865 pattern = 1) : d110 pattern ≤ (0 : Int) + d618 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d110, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2888 pattern childGuard
    simpa only [d110, d618, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d110, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2913 pattern childGuard
    simpa only [d110, d618, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2915 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2916 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d490 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2915 pattern childGuard
    simpa only [d1865, d490, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2917 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d13 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2918 (pattern : Twelve) (guard : d1865 pattern = 1) : d2 pattern ≤ (0 : Int) + d491 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1865, d491, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2917 pattern childGuard
    simpa only [d1865, d491, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2919 (pattern : Twelve) (guard : d1865 pattern = 1) : d30 pattern ≤ (0 : Int) + d516 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d30, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2916 pattern childGuard
    simpa only [d30, d516, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d30, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2918 pattern childGuard
    simpa only [d30, d516, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2920 (pattern : Twelve) (guard : d1865 pattern = 1) : d30 pattern ≤ (0 : Int) + d517 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d30, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2890 pattern childGuard
    simpa only [d30, d517, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d30, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2870 pattern childGuard
    simpa only [d30, d517, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2921 (pattern : Twelve) (guard : d1865 pattern = 1) : d30 pattern ≤ (0 : Int) + d545 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2919 pattern childGuard
    simpa only [d545, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2920 pattern childGuard
    simpa only [d545, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2922 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (0 : Int) + d3 pattern := by
  omega
theorem c2923 (pattern : Twelve) (guard : d0 pattern = 1) : d3 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2924 (pattern : Twelve) (guard : d1865 pattern = 1) : d3 pattern ≤ (0 : Int) + d492 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d1865, d492, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2923 pattern childGuard
    simpa only [d1865, d492, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2925 (pattern : Twelve) (guard : d1865 pattern = 1) : d37 pattern ≤ (0 : Int) + d518 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d37, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d37, d518, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d37, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2924 pattern childGuard
    simpa only [d37, d518, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2926 (pattern : Twelve) (guard : d1865 pattern = 1) : d58 pattern ≤ (0 : Int) + d546 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d58, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2920 pattern childGuard
    simpa only [d58, d546, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d58, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2925 pattern childGuard
    simpa only [d58, d546, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2927 (pattern : Twelve) (guard : d1865 pattern = 1) : d79 pattern ≤ (0 : Int) + d569 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d79, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2921 pattern childGuard
    simpa only [d79, d569, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d79, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2926 pattern childGuard
    simpa only [d79, d569, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2928 (pattern : Twelve) (guard : d1865 pattern = 1) : d30 pattern ≤ (0 : Int) + d547 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2920 pattern childGuard
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2906 pattern childGuard
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2929 (pattern : Twelve) (guard : d1865 pattern = 1) : d80 pattern ≤ (0 : Int) + d570 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d80, d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2928 pattern childGuard
    simpa only [d80, d570, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d80, d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2885 pattern childGuard
    simpa only [d80, d570, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2930 (pattern : Twelve) (guard : d1865 pattern = 1) : d95 pattern ≤ (0 : Int) + d592 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d95, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2927 pattern childGuard
    simpa only [d95, d592, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d95, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2929 pattern childGuard
    simpa only [d95, d592, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2931 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d14 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2932 (pattern : Twelve) (guard : d1865 pattern = 1) : d2 pattern ≤ (0 : Int) + d493 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1865, d493, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2931 pattern childGuard
    simpa only [d1865, d493, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2933 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (0 : Int) + d4 pattern := by
  omega
theorem c2934 (pattern : Twelve) (guard : d1865 pattern = 1) : d4 pattern ≤ (0 : Int) + d494 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d1865, d494, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1334 pattern childGuard
    simpa only [d1865, d494, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2935 (pattern : Twelve) (guard : d1865 pattern = 1) : d38 pattern ≤ (0 : Int) + d519 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d38, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2932 pattern childGuard
    simpa only [d38, d519, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d38, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2934 pattern childGuard
    simpa only [d38, d519, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2936 (pattern : Twelve) (guard : d1865 pattern = 1) : d39 pattern ≤ (0 : Int) + d520 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d39, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2870 pattern childGuard
    simpa only [d39, d520, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d39, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d39, d520, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2937 (pattern : Twelve) (guard : d1865 pattern = 1) : d59 pattern ≤ (0 : Int) + d548 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d59, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2935 pattern childGuard
    simpa only [d59, d548, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d59, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2936 pattern childGuard
    simpa only [d59, d548, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2938 (pattern : Twelve) (guard : d1865 pattern = 1) : d38 pattern ≤ (0 : Int) + d521 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d38, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2870 pattern childGuard
    simpa only [d38, d521, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d38, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2934 pattern childGuard
    simpa only [d38, d521, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2939 (pattern : Twelve) (guard : d1865 pattern = 1) : d40 pattern ≤ (0 : Int) + d520 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d40, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2883 pattern childGuard
    simpa only [d40, d520, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d40, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d40, d520, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
