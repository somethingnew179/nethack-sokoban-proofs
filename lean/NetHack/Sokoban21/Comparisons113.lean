/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons112
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c15820 (pattern : Twelve) (guard : d477 pattern = 1) : d880 pattern ≤ (1 : Int) + d2116 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d880, d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15819 pattern childGuard
    simpa only [d880, d2116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d880, d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d880, d2116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15821 (pattern : Twelve) (guard : d477 pattern = 1) : d887 pattern ≤ (1 : Int) + d2117 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d887, d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15752 pattern childGuard
    simpa only [d887, d2117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d887, d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15820 pattern childGuard
    simpa only [d887, d2117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15822 (pattern : Twelve) (guard : d477 pattern = 1) : d896 pattern ≤ (1 : Int) + d2118 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d896, d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15705 pattern childGuard
    simpa only [d896, d2118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d896, d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15821 pattern childGuard
    simpa only [d896, d2118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15823 (pattern : Twelve) (guard : d477 pattern = 1) : d881 pattern ≤ (1 : Int) + d126 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d881, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15683 pattern childGuard
    simpa only [d881, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d881, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15745 pattern childGuard
    simpa only [d881, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15824 (pattern : Twelve) (guard : d477 pattern = 1) : d888 pattern ≤ (1 : Int) + d134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d888, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15823 pattern childGuard
    simpa only [d888, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d888, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15748 pattern childGuard
    simpa only [d888, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15825 (pattern : Twelve) (guard : d477 pattern = 1) : d889 pattern ≤ (1 : Int) + d2674 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d889, d2674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15714 pattern childGuard
    simpa only [d889, d2674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d889, d2674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d889, d2674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15826 (pattern : Twelve) (guard : d477 pattern = 1) : d897 pattern ≤ (1 : Int) + d2675 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d897, d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15824 pattern childGuard
    simpa only [d897, d2675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d897, d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15825 pattern childGuard
    simpa only [d897, d2675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15827 (pattern : Twelve) (guard : d477 pattern = 1) : d901 pattern ≤ (1 : Int) + d2676 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d901, d2676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15822 pattern childGuard
    simpa only [d901, d2676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d901, d2676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15826 pattern childGuard
    simpa only [d901, d2676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15828 (pattern : Twelve) (guard : d477 pattern = 1) : d903 pattern ≤ (1 : Int) + d2677 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d903, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15818 pattern childGuard
    simpa only [d903, d2677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d903, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15827 pattern childGuard
    simpa only [d903, d2677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15829 (pattern : Twelve) (guard : d477 pattern = 1) : d904 pattern ≤ (1 : Int) + d2678 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d904, d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15810 pattern childGuard
    simpa only [d904, d2678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d904, d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d904, d2678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15830 (pattern : Twelve) (guard : d477 pattern = 1) : d905 pattern ≤ (1 : Int) + d2679 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d905, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15828 pattern childGuard
    simpa only [d905, d2679, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d905, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15829 pattern childGuard
    simpa only [d905, d2679, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15831 (pattern : Twelve) (guard : d477 pattern = 1) : d906 pattern ≤ (1 : Int) + d2680 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d906, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15811 pattern childGuard
    simpa only [d906, d2680, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d906, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15830 pattern childGuard
    simpa only [d906, d2680, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15832 (pattern : Twelve) (guard : d477 pattern = 1) : d907 pattern ≤ (1 : Int) + d2681 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d907, d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15795 pattern childGuard
    simpa only [d907, d2681, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d907, d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15831 pattern childGuard
    simpa only [d907, d2681, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15833 (pattern : Twelve) (guard : d477 pattern = 1) : d1275 pattern ≤ (1 : Int) + d7 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12675 pattern childGuard
    simpa only [d477, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15266 pattern childGuard
    simpa only [d477, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15834 (pattern : Twelve) (guard : d477 pattern = 1) : d1278 pattern ≤ (1 : Int) + d2057 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1278, d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15833 pattern childGuard
    simpa only [d1278, d2057, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1278, d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15797 pattern childGuard
    simpa only [d1278, d2057, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15835 (pattern : Twelve) (guard : d477 pattern = 1) : d1284 pattern ≤ (1 : Int) + d2128 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1284, d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15834 pattern childGuard
    simpa only [d1284, d2128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1284, d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15797 pattern childGuard
    simpa only [d1284, d2128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15836 (pattern : Twelve) (guard : d477 pattern = 1) : d1293 pattern ≤ (1 : Int) + d2129 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1293, d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15657 pattern childGuard
    simpa only [d1293, d2129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1293, d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15835 pattern childGuard
    simpa only [d1293, d2129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15837 (pattern : Twelve) (guard : d477 pattern = 1) : d1294 pattern ≤ (1 : Int) + d2682 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1294, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15665 pattern childGuard
    simpa only [d1294, d2682, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1294, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1294, d2682, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15838 (pattern : Twelve) (guard : d477 pattern = 1) : d1305 pattern ≤ (1 : Int) + d2683 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1305, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15836 pattern childGuard
    simpa only [d1305, d2683, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1305, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15837 pattern childGuard
    simpa only [d1305, d2683, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15839 (pattern : Twelve) (guard : d477 pattern = 1) : d1276 pattern ≤ (1 : Int) + d9 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12682 pattern childGuard
    simpa only [d477, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11185 pattern childGuard
    simpa only [d477, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15840 (pattern : Twelve) (guard : d477 pattern = 1) : d1279 pattern ≤ (1 : Int) + d2060 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1279, d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15833 pattern childGuard
    simpa only [d1279, d2060, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1279, d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15839 pattern childGuard
    simpa only [d1279, d2060, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15841 (pattern : Twelve) (guard : d477 pattern = 1) : d1280 pattern ≤ (1 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1280, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15797 pattern childGuard
    simpa only [d1280, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1280, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1280, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15842 (pattern : Twelve) (guard : d477 pattern = 1) : d1285 pattern ≤ (1 : Int) + d2134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1285, d2134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15840 pattern childGuard
    simpa only [d1285, d2134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1285, d2134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15841 pattern childGuard
    simpa only [d1285, d2134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15843 (pattern : Twelve) (guard : d477 pattern = 1) : d1295 pattern ≤ (1 : Int) + d2135 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1295, d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15773 pattern childGuard
    simpa only [d1295, d2135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1295, d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15842 pattern childGuard
    simpa only [d1295, d2135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15844 (pattern : Twelve) (guard : d477 pattern = 1) : d1286 pattern ≤ (1 : Int) + d2684 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1286, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15766 pattern childGuard
    simpa only [d1286, d2684, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1286, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15667 pattern childGuard
    simpa only [d1286, d2684, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15845 (pattern : Twelve) (guard : d477 pattern = 1) : d1296 pattern ≤ (1 : Int) + d2685 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1296, d2685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15844 pattern childGuard
    simpa only [d1296, d2685, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1296, d2685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1296, d2685, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15846 (pattern : Twelve) (guard : d477 pattern = 1) : d1306 pattern ≤ (1 : Int) + d2686 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1306, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15843 pattern childGuard
    simpa only [d1306, d2686, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1306, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15845 pattern childGuard
    simpa only [d1306, d2686, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15847 (pattern : Twelve) (guard : d477 pattern = 1) : d1313 pattern ≤ (1 : Int) + d2687 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1313, d2687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15838 pattern childGuard
    simpa only [d1313, d2687, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1313, d2687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15846 pattern childGuard
    simpa only [d1313, d2687, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15848 (pattern : Twelve) (guard : d477 pattern = 1) : d1281 pattern ≤ (1 : Int) + d46 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1281, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15797 pattern childGuard
    simpa only [d1281, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1281, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15747 pattern childGuard
    simpa only [d1281, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15849 (pattern : Twelve) (guard : d477 pattern = 1) : d1287 pattern ≤ (1 : Int) + d2140 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1287, d2140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15840 pattern childGuard
    simpa only [d1287, d2140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1287, d2140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15848 pattern childGuard
    simpa only [d1287, d2140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15850 (pattern : Twelve) (guard : d477 pattern = 1) : d1297 pattern ≤ (1 : Int) + d2141 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1297, d2141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15684 pattern childGuard
    simpa only [d1297, d2141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1297, d2141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15849 pattern childGuard
    simpa only [d1297, d2141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15851 (pattern : Twelve) (guard : d477 pattern = 1) : d1298 pattern ≤ (1 : Int) + d2688 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1298, d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15766 pattern childGuard
    simpa only [d1298, d2688, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1298, d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1298, d2688, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15852 (pattern : Twelve) (guard : d477 pattern = 1) : d1307 pattern ≤ (1 : Int) + d2689 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1307, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15850 pattern childGuard
    simpa only [d1307, d2689, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1307, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15851 pattern childGuard
    simpa only [d1307, d2689, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15853 (pattern : Twelve) (guard : d477 pattern = 1) : d1277 pattern ≤ (1 : Int) + d15 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12731 pattern childGuard
    simpa only [d477, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11886 pattern childGuard
    simpa only [d477, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15854 (pattern : Twelve) (guard : d477 pattern = 1) : d1282 pattern ≤ (1 : Int) + d2087 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1282, d2087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15839 pattern childGuard
    simpa only [d1282, d2087, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1282, d2087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15853 pattern childGuard
    simpa only [d1282, d2087, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15855 (pattern : Twelve) (guard : d477 pattern = 1) : d1288 pattern ≤ (1 : Int) + d2144 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1288, d2144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15854 pattern childGuard
    simpa only [d1288, d2144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1288, d2144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15748 pattern childGuard
    simpa only [d1288, d2144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15856 (pattern : Twelve) (guard : d477 pattern = 1) : d1299 pattern ≤ (1 : Int) + d2145 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1299, d2145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15786 pattern childGuard
    simpa only [d1299, d2145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1299, d2145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15855 pattern childGuard
    simpa only [d1299, d2145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15857 (pattern : Twelve) (guard : d477 pattern = 1) : d1289 pattern ≤ (1 : Int) + d2238 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1289, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15787 pattern childGuard
    simpa only [d1289, d2238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1289, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15714 pattern childGuard
    simpa only [d1289, d2238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15858 (pattern : Twelve) (guard : d477 pattern = 1) : d1300 pattern ≤ (1 : Int) + d2690 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1300, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15857 pattern childGuard
    simpa only [d1300, d2690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1300, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1300, d2690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15859 (pattern : Twelve) (guard : d477 pattern = 1) : d1308 pattern ≤ (1 : Int) + d2691 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1308, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15856 pattern childGuard
    simpa only [d1308, d2691, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1308, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15858 pattern childGuard
    simpa only [d1308, d2691, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15860 (pattern : Twelve) (guard : d477 pattern = 1) : d1314 pattern ≤ (1 : Int) + d2692 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1314, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15852 pattern childGuard
    simpa only [d1314, d2692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1314, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15859 pattern childGuard
    simpa only [d1314, d2692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15861 (pattern : Twelve) (guard : d477 pattern = 1) : d1315 pattern ≤ (1 : Int) + d2693 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1315, d2693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15846 pattern childGuard
    simpa only [d1315, d2693, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1315, d2693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1315, d2693, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15862 (pattern : Twelve) (guard : d477 pattern = 1) : d1319 pattern ≤ (1 : Int) + d2694 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1319, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15860 pattern childGuard
    simpa only [d1319, d2694, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1319, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15861 pattern childGuard
    simpa only [d1319, d2694, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15863 (pattern : Twelve) (guard : d477 pattern = 1) : d1321 pattern ≤ (1 : Int) + d2695 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1321, d2695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15847 pattern childGuard
    simpa only [d1321, d2695, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1321, d2695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15862 pattern childGuard
    simpa only [d1321, d2695, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15864 (pattern : Twelve) (guard : d477 pattern = 1) : d1324 pattern ≤ (1 : Int) + d11 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12686 pattern childGuard
    simpa only [d477, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12182 pattern childGuard
    simpa only [d477, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15865 (pattern : Twelve) (guard : d477 pattern = 1) : d1325 pattern ≤ (1 : Int) + d2696 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1325, d2696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15833 pattern childGuard
    simpa only [d1325, d2696, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1325, d2696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15864 pattern childGuard
    simpa only [d1325, d2696, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15866 (pattern : Twelve) (guard : d477 pattern = 1) : d1326 pattern ≤ (1 : Int) + d2697 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1326, d2697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15797 pattern childGuard
    simpa only [d1326, d2697, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1326, d2697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15864 pattern childGuard
    simpa only [d1326, d2697, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15867 (pattern : Twelve) (guard : d477 pattern = 1) : d1333 pattern ≤ (1 : Int) + d2698 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1333, d2698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15865 pattern childGuard
    simpa only [d1333, d2698, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1333, d2698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15866 pattern childGuard
    simpa only [d1333, d2698, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15868 (pattern : Twelve) (guard : d477 pattern = 1) : d1339 pattern ≤ (1 : Int) + d2699 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1339, d2699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15657 pattern childGuard
    simpa only [d1339, d2699, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1339, d2699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15867 pattern childGuard
    simpa only [d1339, d2699, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15869 (pattern : Twelve) (guard : d477 pattern = 1) : d1345 pattern ≤ (1 : Int) + d2700 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1345, d2700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15868 pattern childGuard
    simpa only [d1345, d2700, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1345, d2700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15837 pattern childGuard
    simpa only [d1345, d2700, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15870 (pattern : Twelve) (guard : d477 pattern = 1) : d1327 pattern ≤ (1 : Int) + d2079 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1327, d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15833 pattern childGuard
    simpa only [d1327, d2079, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1327, d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15747 pattern childGuard
    simpa only [d1327, d2079, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15871 (pattern : Twelve) (guard : d477 pattern = 1) : d1334 pattern ≤ (1 : Int) + d2164 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1334, d2164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15870 pattern childGuard
    simpa only [d1334, d2164, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1334, d2164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15841 pattern childGuard
    simpa only [d1334, d2164, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15872 (pattern : Twelve) (guard : d477 pattern = 1) : d1340 pattern ≤ (1 : Int) + d2165 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1340, d2165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15773 pattern childGuard
    simpa only [d1340, d2165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1340, d2165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15871 pattern childGuard
    simpa only [d1340, d2165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15873 (pattern : Twelve) (guard : d477 pattern = 1) : d1346 pattern ≤ (1 : Int) + d2701 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1346, d2701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15872 pattern childGuard
    simpa only [d1346, d2701, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1346, d2701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15845 pattern childGuard
    simpa only [d1346, d2701, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15874 (pattern : Twelve) (guard : d477 pattern = 1) : d1349 pattern ≤ (1 : Int) + d2702 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1349, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15869 pattern childGuard
    simpa only [d1349, d2702, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1349, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15873 pattern childGuard
    simpa only [d1349, d2702, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15875 (pattern : Twelve) (guard : d477 pattern = 1) : d1328 pattern ≤ (1 : Int) + d2169 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1328, d2169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15797 pattern childGuard
    simpa only [d1328, d2169, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1328, d2169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15853 pattern childGuard
    simpa only [d1328, d2169, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15876 (pattern : Twelve) (guard : d477 pattern = 1) : d1335 pattern ≤ (1 : Int) + d2170 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1335, d2170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15870 pattern childGuard
    simpa only [d1335, d2170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1335, d2170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15875 pattern childGuard
    simpa only [d1335, d2170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15877 (pattern : Twelve) (guard : d477 pattern = 1) : d1341 pattern ≤ (1 : Int) + d2171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1341, d2171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15684 pattern childGuard
    simpa only [d1341, d2171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1341, d2171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15876 pattern childGuard
    simpa only [d1341, d2171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15878 (pattern : Twelve) (guard : d477 pattern = 1) : d1329 pattern ≤ (1 : Int) + d2703 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1329, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15665 pattern childGuard
    simpa only [d1329, d2703, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1329, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15672 pattern childGuard
    simpa only [d1329, d2703, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15879 (pattern : Twelve) (guard : d477 pattern = 1) : d1336 pattern ≤ (1 : Int) + d2704 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1336, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15766 pattern childGuard
    simpa only [d1336, d2704, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1336, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15878 pattern childGuard
    simpa only [d1336, d2704, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15880 (pattern : Twelve) (guard : d477 pattern = 1) : d1342 pattern ≤ (1 : Int) + d2705 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1342, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15879 pattern childGuard
    simpa only [d1342, d2705, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1342, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1342, d2705, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15881 (pattern : Twelve) (guard : d477 pattern = 1) : d1347 pattern ≤ (1 : Int) + d2706 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1347, d2706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15877 pattern childGuard
    simpa only [d1347, d2706, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1347, d2706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15880 pattern childGuard
    simpa only [d1347, d2706, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15882 (pattern : Twelve) (guard : d477 pattern = 1) : d1330 pattern ≤ (1 : Int) + d2084 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1330, d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15839 pattern childGuard
    simpa only [d1330, d2084, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1330, d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1330, d2084, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15883 (pattern : Twelve) (guard : d477 pattern = 1) : d1331 pattern ≤ (1 : Int) + d2176 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1331, d2176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15853 pattern childGuard
    simpa only [d1331, d2176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1331, d2176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1331, d2176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15884 (pattern : Twelve) (guard : d477 pattern = 1) : d1337 pattern ≤ (1 : Int) + d2177 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1337, d2177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15882 pattern childGuard
    simpa only [d1337, d2177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1337, d2177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15883 pattern childGuard
    simpa only [d1337, d2177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15885 (pattern : Twelve) (guard : d477 pattern = 1) : d1343 pattern ≤ (1 : Int) + d2178 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1343, d2178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15786 pattern childGuard
    simpa only [d1343, d2178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1343, d2178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15884 pattern childGuard
    simpa only [d1343, d2178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15886 (pattern : Twelve) (guard : d477 pattern = 1) : d1332 pattern ≤ (1 : Int) + d2707 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1332, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15713 pattern childGuard
    simpa only [d1332, d2707, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1332, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15679 pattern childGuard
    simpa only [d1332, d2707, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15887 (pattern : Twelve) (guard : d477 pattern = 1) : d1338 pattern ≤ (1 : Int) + d2708 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1338, d2708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15886 pattern childGuard
    simpa only [d1338, d2708, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1338, d2708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15753 pattern childGuard
    simpa only [d1338, d2708, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15888 (pattern : Twelve) (guard : d477 pattern = 1) : d1344 pattern ≤ (1 : Int) + d2709 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1344, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15887 pattern childGuard
    simpa only [d1344, d2709, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1344, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1344, d2709, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15889 (pattern : Twelve) (guard : d477 pattern = 1) : d1348 pattern ≤ (1 : Int) + d2710 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1348, d2710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15885 pattern childGuard
    simpa only [d1348, d2710, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1348, d2710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15888 pattern childGuard
    simpa only [d1348, d2710, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15890 (pattern : Twelve) (guard : d477 pattern = 1) : d1350 pattern ≤ (1 : Int) + d2711 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1350, d2711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15881 pattern childGuard
    simpa only [d1350, d2711, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1350, d2711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15889 pattern childGuard
    simpa only [d1350, d2711, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15891 (pattern : Twelve) (guard : d477 pattern = 1) : d1351 pattern ≤ (1 : Int) + d2712 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1351, d2712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15873 pattern childGuard
    simpa only [d1351, d2712, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1351, d2712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1351, d2712, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15892 (pattern : Twelve) (guard : d477 pattern = 1) : d1352 pattern ≤ (1 : Int) + d2713 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1352, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15890 pattern childGuard
    simpa only [d1352, d2713, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1352, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15891 pattern childGuard
    simpa only [d1352, d2713, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15893 (pattern : Twelve) (guard : d477 pattern = 1) : d1353 pattern ≤ (1 : Int) + d2714 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1353, d2714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15874 pattern childGuard
    simpa only [d1353, d2714, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1353, d2714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15892 pattern childGuard
    simpa only [d1353, d2714, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15894 (pattern : Twelve) (guard : d477 pattern = 1) : d1354 pattern ≤ (1 : Int) + d2715 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1354, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15863 pattern childGuard
    simpa only [d1354, d2715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1354, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15893 pattern childGuard
    simpa only [d1354, d2715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15895 (pattern : Twelve) (guard : d477 pattern = 1) : d1649 pattern ≤ (1 : Int) + d2716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1649, d2716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15665 pattern childGuard
    simpa only [d1649, d2716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1649, d2716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15864 pattern childGuard
    simpa only [d1649, d2716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15896 (pattern : Twelve) (guard : d477 pattern = 1) : d1650 pattern ≤ (1 : Int) + d2717 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1650, d2717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15713 pattern childGuard
    simpa only [d1650, d2717, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1650, d2717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1650, d2717, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15897 (pattern : Twelve) (guard : d477 pattern = 1) : d1656 pattern ≤ (1 : Int) + d2718 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1656, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15895 pattern childGuard
    simpa only [d1656, d2718, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1656, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15896 pattern childGuard
    simpa only [d1656, d2718, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15898 (pattern : Twelve) (guard : d477 pattern = 1) : d1644 pattern ≤ (1 : Int) + d2130 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1644, d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15864 pattern childGuard
    simpa only [d1644, d2130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1644, d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15672 pattern childGuard
    simpa only [d1644, d2130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15899 (pattern : Twelve) (guard : d477 pattern = 1) : d1645 pattern ≤ (1 : Int) + d2061 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1645, d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15864 pattern childGuard
    simpa only [d1645, d2061, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1645, d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1645, d2061, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15900 (pattern : Twelve) (guard : d477 pattern = 1) : d1647 pattern ≤ (1 : Int) + d2196 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1647, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15898 pattern childGuard
    simpa only [d1647, d2196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1647, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15899 pattern childGuard
    simpa only [d1647, d2196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15901 (pattern : Twelve) (guard : d477 pattern = 1) : d1651 pattern ≤ (1 : Int) + d2719 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1651, d2719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15844 pattern childGuard
    simpa only [d1651, d2719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1651, d2719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15900 pattern childGuard
    simpa only [d1651, d2719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15902 (pattern : Twelve) (guard : d477 pattern = 1) : d1657 pattern ≤ (1 : Int) + d2720 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1657, d2720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15901 pattern childGuard
    simpa only [d1657, d2720, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1657, d2720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15858 pattern childGuard
    simpa only [d1657, d2720, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15903 (pattern : Twelve) (guard : d477 pattern = 1) : d1660 pattern ≤ (1 : Int) + d2721 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1660, d2721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15897 pattern childGuard
    simpa only [d1660, d2721, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1660, d2721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15902 pattern childGuard
    simpa only [d1660, d2721, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15904 (pattern : Twelve) (guard : d477 pattern = 1) : d1652 pattern ≤ (1 : Int) + d2722 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1652, d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15766 pattern childGuard
    simpa only [d1652, d2722, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1652, d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15898 pattern childGuard
    simpa only [d1652, d2722, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15905 (pattern : Twelve) (guard : d477 pattern = 1) : d1653 pattern ≤ (1 : Int) + d2723 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1653, d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15787 pattern childGuard
    simpa only [d1653, d2723, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1653, d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1653, d2723, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15906 (pattern : Twelve) (guard : d477 pattern = 1) : d1658 pattern ≤ (1 : Int) + d2724 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1658, d2724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15904 pattern childGuard
    simpa only [d1658, d2724, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1658, d2724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15905 pattern childGuard
    simpa only [d1658, d2724, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15907 (pattern : Twelve) (guard : d477 pattern = 1) : d1646 pattern ≤ (1 : Int) + d2147 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1646, d2147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15672 pattern childGuard
    simpa only [d1646, d2147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1646, d2147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15679 pattern childGuard
    simpa only [d1646, d2147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15908 (pattern : Twelve) (guard : d477 pattern = 1) : d1648 pattern ≤ (1 : Int) + d2206 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1648, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15907 pattern childGuard
    simpa only [d1648, d2206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1648, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15753 pattern childGuard
    simpa only [d1648, d2206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15909 (pattern : Twelve) (guard : d477 pattern = 1) : d1654 pattern ≤ (1 : Int) + d2725 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1654, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15857 pattern childGuard
    simpa only [d1654, d2725, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1654, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15908 pattern childGuard
    simpa only [d1654, d2725, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15910 (pattern : Twelve) (guard : d477 pattern = 1) : d1655 pattern ≤ (1 : Int) + d2726 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1655, d2726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15788 pattern childGuard
    simpa only [d1655, d2726, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1655, d2726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1655, d2726, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15911 (pattern : Twelve) (guard : d477 pattern = 1) : d1659 pattern ≤ (1 : Int) + d2727 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1659, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15909 pattern childGuard
    simpa only [d1659, d2727, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1659, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15910 pattern childGuard
    simpa only [d1659, d2727, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15912 (pattern : Twelve) (guard : d477 pattern = 1) : d1661 pattern ≤ (1 : Int) + d2728 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1661, d2728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15906 pattern childGuard
    simpa only [d1661, d2728, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1661, d2728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15911 pattern childGuard
    simpa only [d1661, d2728, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15913 (pattern : Twelve) (guard : d477 pattern = 1) : d1662 pattern ≤ (1 : Int) + d2729 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1662, d2729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15902 pattern childGuard
    simpa only [d1662, d2729, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1662, d2729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1662, d2729, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15914 (pattern : Twelve) (guard : d477 pattern = 1) : d1663 pattern ≤ (1 : Int) + d2730 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1663, d2730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15912 pattern childGuard
    simpa only [d1663, d2730, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1663, d2730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15913 pattern childGuard
    simpa only [d1663, d2730, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15915 (pattern : Twelve) (guard : d477 pattern = 1) : d1664 pattern ≤ (1 : Int) + d2731 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1664, d2731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15903 pattern childGuard
    simpa only [d1664, d2731, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1664, d2731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15914 pattern childGuard
    simpa only [d1664, d2731, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15916 (pattern : Twelve) (guard : d477 pattern = 1) : d1668 pattern ≤ (1 : Int) + d2732 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1668, d2732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15665 pattern childGuard
    simpa only [d1668, d2732, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1668, d2732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15898 pattern childGuard
    simpa only [d1668, d2732, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15917 (pattern : Twelve) (guard : d477 pattern = 1) : d1671 pattern ≤ (1 : Int) + d2733 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1671, d2733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15916 pattern childGuard
    simpa only [d1671, d2733, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1671, d2733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15896 pattern childGuard
    simpa only [d1671, d2733, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15918 (pattern : Twelve) (guard : d477 pattern = 1) : d1674 pattern ≤ (1 : Int) + d2734 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1674, d2734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15917 pattern childGuard
    simpa only [d1674, d2734, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1674, d2734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15902 pattern childGuard
    simpa only [d1674, d2734, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15919 (pattern : Twelve) (guard : d477 pattern = 1) : d1665 pattern ≤ (1 : Int) + d2160 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1665, d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15864 pattern childGuard
    simpa only [d1665, d2160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1665, d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15679 pattern childGuard
    simpa only [d1665, d2160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15920 (pattern : Twelve) (guard : d477 pattern = 1) : d1666 pattern ≤ (1 : Int) + d2735 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1666, d2735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15898 pattern childGuard
    simpa only [d1666, d2735, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1666, d2735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15919 pattern childGuard
    simpa only [d1666, d2735, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15921 (pattern : Twelve) (guard : d477 pattern = 1) : d1669 pattern ≤ (1 : Int) + d2736 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1669, d2736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15766 pattern childGuard
    simpa only [d1669, d2736, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1669, d2736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15920 pattern childGuard
    simpa only [d1669, d2736, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15922 (pattern : Twelve) (guard : d477 pattern = 1) : d1672 pattern ≤ (1 : Int) + d2737 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1672, d2737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15921 pattern childGuard
    simpa only [d1672, d2737, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1672, d2737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15858 pattern childGuard
    simpa only [d1672, d2737, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15923 (pattern : Twelve) (guard : d477 pattern = 1) : d183 pattern ≤ (1 : Int) + d2148 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d183, d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15679 pattern childGuard
    simpa only [d183, d2148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d183, d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d183, d2148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15924 (pattern : Twelve) (guard : d477 pattern = 1) : d1667 pattern ≤ (1 : Int) + d2738 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1667, d2738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15753 pattern childGuard
    simpa only [d1667, d2738, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1667, d2738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15923 pattern childGuard
    simpa only [d1667, d2738, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15925 (pattern : Twelve) (guard : d477 pattern = 1) : d1670 pattern ≤ (1 : Int) + d2739 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1670, d2739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15857 pattern childGuard
    simpa only [d1670, d2739, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1670, d2739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15924 pattern childGuard
    simpa only [d1670, d2739, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15926 (pattern : Twelve) (guard : d477 pattern = 1) : d1252 pattern ≤ (1 : Int) + d2257 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1252, d2257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15788 pattern childGuard
    simpa only [d1252, d2257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1252, d2257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1252, d2257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15927 (pattern : Twelve) (guard : d477 pattern = 1) : d1626 pattern ≤ (1 : Int) + d2740 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1626, d2740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15926 pattern childGuard
    simpa only [d1626, d2740, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1626, d2740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d1626, d2740, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15928 (pattern : Twelve) (guard : d477 pattern = 1) : d1673 pattern ≤ (1 : Int) + d2741 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1673, d2741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15925 pattern childGuard
    simpa only [d1673, d2741, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1673, d2741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15927 pattern childGuard
    simpa only [d1673, d2741, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15929 (pattern : Twelve) (guard : d477 pattern = 1) : d1675 pattern ≤ (1 : Int) + d2742 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1675, d2742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15922 pattern childGuard
    simpa only [d1675, d2742, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1675, d2742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15928 pattern childGuard
    simpa only [d1675, d2742, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15930 (pattern : Twelve) (guard : d477 pattern = 1) : d1676 pattern ≤ (1 : Int) + d2743 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1676, d2743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15929 pattern childGuard
    simpa only [d1676, d2743, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1676, d2743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15913 pattern childGuard
    simpa only [d1676, d2743, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15931 (pattern : Twelve) (guard : d477 pattern = 1) : d1677 pattern ≤ (1 : Int) + d2744 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1677, d2744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15918 pattern childGuard
    simpa only [d1677, d2744, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1677, d2744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15930 pattern childGuard
    simpa only [d1677, d2744, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15932 (pattern : Twelve) (guard : d477 pattern = 1) : d1678 pattern ≤ (1 : Int) + d2745 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d1678, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15915 pattern childGuard
    simpa only [d1678, d2745, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d1678, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15931 pattern childGuard
    simpa only [d1678, d2745, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15933 (pattern : Twelve) (guard : d2746 pattern = 1) : d0 pattern ≤ (1 : Int) + d0 pattern := by
  omega
theorem c15934 (pattern : Twelve) (guard : d7 pattern = 1) : d0 pattern ≤ (1 : Int) + d0 pattern := by
  omega
theorem c15935 (pattern : Twelve) (guard : d2746 pattern = 1) : d477 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15934 pattern childGuard
    simpa only [d2746, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12209 pattern childGuard
    simpa only [d2746, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15936 (pattern : Twelve) (guard : d2746 pattern = 1) : d498 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15933 pattern childGuard
    simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15935 pattern childGuard
    simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15937 (pattern : Twelve) (guard : d2746 pattern = 1) : d478 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15934 pattern childGuard
    simpa only [d2746, d478, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12212 pattern childGuard
    simpa only [d2746, d478, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15938 (pattern : Twelve) (guard : d2746 pattern = 1) : d499 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15933 pattern childGuard
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15937 pattern childGuard
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15939 (pattern : Twelve) (guard : d2746 pattern = 1) : d532 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15936 pattern childGuard
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15938 pattern childGuard
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15940 (pattern : Twelve) (guard : d7 pattern = 1) : d1 pattern ≤ (1 : Int) + d1 pattern := by
  omega
theorem c15941 (pattern : Twelve) (guard : d2746 pattern = 1) : d161 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15940 pattern childGuard
    simpa only [d2746, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12218 pattern childGuard
    simpa only [d2746, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15942 (pattern : Twelve) (guard : d2746 pattern = 1) : d171 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15933 pattern childGuard
    simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15941 pattern childGuard
    simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15943 (pattern : Twelve) (guard : d2746 pattern = 1) : d162 pattern ≤ (1 : Int) + d477 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d162, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15934 pattern childGuard
    simpa only [d2746, d162, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d162, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12221 pattern childGuard
    simpa only [d2746, d162, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15944 (pattern : Twelve) (guard : d2746 pattern = 1) : d479 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15940 pattern childGuard
    simpa only [d2746, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11094 pattern childGuard
    simpa only [d2746, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15945 (pattern : Twelve) (guard : d2746 pattern = 1) : d500 pattern ≤ (1 : Int) + d2747 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d500, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15943 pattern childGuard
    simpa only [d500, d2747, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d500, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15944 pattern childGuard
    simpa only [d500, d2747, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15946 (pattern : Twelve) (guard : d2746 pattern = 1) : d533 pattern ≤ (1 : Int) + d2748 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d533, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15942 pattern childGuard
    simpa only [d533, d2748, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d533, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15945 pattern childGuard
    simpa only [d533, d2748, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15947 (pattern : Twelve) (guard : d2746 pattern = 1) : d561 pattern ≤ (1 : Int) + d2749 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d561, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15939 pattern childGuard
    simpa only [d561, d2749, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d561, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15946 pattern childGuard
    simpa only [d561, d2749, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15948 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15949 (pattern : Twelve) (guard : d2746 pattern = 1) : d162 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15934 pattern childGuard
    simpa only [d2746, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15948 pattern childGuard
    simpa only [d2746, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15950 (pattern : Twelve) (guard : d2746 pattern = 1) : d480 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15934 pattern childGuard
    simpa only [d2746, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11159 pattern childGuard
    simpa only [d2746, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15951 (pattern : Twelve) (guard : d2746 pattern = 1) : d501 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15949 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15950 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15952 (pattern : Twelve) (guard : d2746 pattern = 1) : d534 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15938 pattern childGuard
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15951 pattern childGuard
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15953 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (1 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15954 (pattern : Twelve) (guard : d7 pattern = 1) : d8 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15953 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15955 (pattern : Twelve) (guard : d2746 pattern = 1) : d481 pattern ≤ (1 : Int) + d2750 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d481, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15954 pattern childGuard
    simpa only [d2746, d481, d2750, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d481, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12318 pattern childGuard
    simpa only [d2746, d481, d2750, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15956 (pattern : Twelve) (guard : d2746 pattern = 1) : d502 pattern ≤ (1 : Int) + d2751 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d502, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15943 pattern childGuard
    simpa only [d502, d2751, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d502, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15955 pattern childGuard
    simpa only [d502, d2751, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15957 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (1 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15958 (pattern : Twelve) (guard : d7 pattern = 1) : d10 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15957 pattern childGuard
    simpa only [d7, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d7, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15959 (pattern : Twelve) (guard : d2746 pattern = 1) : d482 pattern ≤ (1 : Int) + d2750 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d482, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15958 pattern childGuard
    simpa only [d2746, d482, d2750, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d482, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12318 pattern childGuard
    simpa only [d2746, d482, d2750, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
