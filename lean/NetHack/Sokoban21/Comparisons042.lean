/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons041
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c5880 (pattern : Twelve) (guard : d0 pattern = 1) : d394 pattern ≤ (0 : Int) + d202 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5881 (pattern : Twelve) (guard : d1864 pattern = 1) : d404 pattern ≤ (0 : Int) + d307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d404, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5879 pattern childGuard
    simpa only [d1864, d404, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d404, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5880 pattern childGuard
    simpa only [d1864, d404, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5882 (pattern : Twelve) (guard : d1864 pattern = 1) : d410 pattern ≤ (0 : Int) + d321 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d410, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5877 pattern childGuard
    simpa only [d410, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d410, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5881 pattern childGuard
    simpa only [d410, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5883 (pattern : Twelve) (guard : d1864 pattern = 1) : d415 pattern ≤ (0 : Int) + d332 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d415, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5873 pattern childGuard
    simpa only [d415, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d415, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5882 pattern childGuard
    simpa only [d415, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5884 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d37 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5885 (pattern : Twelve) (guard : d1849 pattern = 1) : d382 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d382, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5019 pattern childGuard
    simpa only [d1849, d382, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d382, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5884 pattern childGuard
    simpa only [d1849, d382, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5886 (pattern : Twelve) (guard : d1863 pattern = 1) : d395 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d395, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5277 pattern childGuard
    simpa only [d1863, d395, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d395, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5885 pattern childGuard
    simpa only [d1863, d395, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5887 (pattern : Twelve) (guard : d0 pattern = 1) : d396 pattern ≤ (0 : Int) + d204 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5888 (pattern : Twelve) (guard : d1864 pattern = 1) : d405 pattern ≤ (0 : Int) + d308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d405, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5886 pattern childGuard
    simpa only [d1864, d405, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d405, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5887 pattern childGuard
    simpa only [d1864, d405, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5889 (pattern : Twelve) (guard : d1849 pattern = 1) : d384 pattern ≤ (0 : Int) + d60 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d384, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5028 pattern childGuard
    simpa only [d1849, d384, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d384, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2583 pattern childGuard
    simpa only [d1849, d384, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5890 (pattern : Twelve) (guard : d1863 pattern = 1) : d397 pattern ≤ (0 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d397, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d1863, d397, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d397, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5889 pattern childGuard
    simpa only [d1863, d397, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5891 (pattern : Twelve) (guard : d0 pattern = 1) : d398 pattern ≤ (0 : Int) + d206 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5892 (pattern : Twelve) (guard : d1864 pattern = 1) : d406 pattern ≤ (0 : Int) + d309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d406, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5890 pattern childGuard
    simpa only [d1864, d406, d309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d406, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5891 pattern childGuard
    simpa only [d1864, d406, d309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5893 (pattern : Twelve) (guard : d1864 pattern = 1) : d411 pattern ≤ (0 : Int) + d322 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d411, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5888 pattern childGuard
    simpa only [d411, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d411, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5892 pattern childGuard
    simpa only [d411, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5894 (pattern : Twelve) (guard : d1863 pattern = 1) : d399 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d399, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5271 pattern childGuard
    simpa only [d1863, d399, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d399, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5878 pattern childGuard
    simpa only [d1863, d399, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5895 (pattern : Twelve) (guard : d0 pattern = 1) : d394 pattern ≤ (0 : Int) + d206 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5896 (pattern : Twelve) (guard : d1864 pattern = 1) : d407 pattern ≤ (0 : Int) + d310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d407, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5894 pattern childGuard
    simpa only [d1864, d407, d310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d407, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5895 pattern childGuard
    simpa only [d1864, d407, d310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5897 (pattern : Twelve) (guard : d1864 pattern = 1) : d412 pattern ≤ (0 : Int) + d323 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d412, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5896 pattern childGuard
    simpa only [d412, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d412, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2593 pattern childGuard
    simpa only [d412, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5898 (pattern : Twelve) (guard : d1864 pattern = 1) : d416 pattern ≤ (0 : Int) + d333 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d416, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5893 pattern childGuard
    simpa only [d416, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d416, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5897 pattern childGuard
    simpa only [d416, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5899 (pattern : Twelve) (guard : d1864 pattern = 1) : d419 pattern ≤ (0 : Int) + d338 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d419, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5883 pattern childGuard
    simpa only [d419, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d419, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5898 pattern childGuard
    simpa only [d419, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5900 (pattern : Twelve) (guard : d1849 pattern = 1) : d380 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d380, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5048 pattern childGuard
    simpa only [d1849, d380, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d380, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5874 pattern childGuard
    simpa only [d1849, d380, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5901 (pattern : Twelve) (guard : d1863 pattern = 1) : d399 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d399, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5045 pattern childGuard
    simpa only [d1863, d399, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d399, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5900 pattern childGuard
    simpa only [d1863, d399, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5902 (pattern : Twelve) (guard : d0 pattern = 1) : d394 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5903 (pattern : Twelve) (guard : d1864 pattern = 1) : d407 pattern ≤ (0 : Int) + d311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d407, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5901 pattern childGuard
    simpa only [d1864, d407, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d407, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5902 pattern childGuard
    simpa only [d1864, d407, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5904 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d43 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5905 (pattern : Twelve) (guard : d1849 pattern = 1) : d380 pattern ≤ (0 : Int) + d62 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d380, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1849, d380, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d380, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5904 pattern childGuard
    simpa only [d1849, d380, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5906 (pattern : Twelve) (guard : d1863 pattern = 1) : d399 pattern ≤ (0 : Int) + d83 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d399, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5303 pattern childGuard
    simpa only [d1863, d399, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d399, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5905 pattern childGuard
    simpa only [d1863, d399, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5907 (pattern : Twelve) (guard : d1864 pattern = 1) : d407 pattern ≤ (0 : Int) + d312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d407, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5906 pattern childGuard
    simpa only [d1864, d407, d312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d407, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5902 pattern childGuard
    simpa only [d1864, d407, d312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5908 (pattern : Twelve) (guard : d1864 pattern = 1) : d407 pattern ≤ (0 : Int) + d324 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5903 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5907 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5909 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d45 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5910 (pattern : Twelve) (guard : d1849 pattern = 1) : d380 pattern ≤ (0 : Int) + d65 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d380, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1849, d380, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d380, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5909 pattern childGuard
    simpa only [d1849, d380, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5911 (pattern : Twelve) (guard : d1863 pattern = 1) : d399 pattern ≤ (0 : Int) + d85 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d399, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5271 pattern childGuard
    simpa only [d1863, d399, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d399, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5910 pattern childGuard
    simpa only [d1863, d399, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5912 (pattern : Twelve) (guard : d1864 pattern = 1) : d407 pattern ≤ (0 : Int) + d313 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d407, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5911 pattern childGuard
    simpa only [d1864, d407, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d407, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5902 pattern childGuard
    simpa only [d1864, d407, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5913 (pattern : Twelve) (guard : d1864 pattern = 1) : d407 pattern ≤ (0 : Int) + d325 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5903 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5912 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5914 (pattern : Twelve) (guard : d1864 pattern = 1) : d407 pattern ≤ (0 : Int) + d334 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5908 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5913 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5915 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d46 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5916 (pattern : Twelve) (guard : d1849 pattern = 1) : d380 pattern ≤ (0 : Int) + d67 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d380, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1849, d380, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d380, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5915 pattern childGuard
    simpa only [d1849, d380, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5917 (pattern : Twelve) (guard : d1863 pattern = 1) : d399 pattern ≤ (0 : Int) + d87 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d399, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1863, d399, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d399, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5916 pattern childGuard
    simpa only [d1863, d399, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5918 (pattern : Twelve) (guard : d1864 pattern = 1) : d407 pattern ≤ (0 : Int) + d314 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d407, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5917 pattern childGuard
    simpa only [d1864, d407, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d407, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5902 pattern childGuard
    simpa only [d1864, d407, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5919 (pattern : Twelve) (guard : d0 pattern = 1) : d40 pattern ≤ (0 : Int) + d47 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5920 (pattern : Twelve) (guard : d1849 pattern = 1) : d384 pattern ≤ (0 : Int) + d69 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d384, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5028 pattern childGuard
    simpa only [d1849, d384, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d384, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5919 pattern childGuard
    simpa only [d1849, d384, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5921 (pattern : Twelve) (guard : d1863 pattern = 1) : d397 pattern ≤ (0 : Int) + d89 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d397, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d1863, d397, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d397, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5920 pattern childGuard
    simpa only [d1863, d397, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5922 (pattern : Twelve) (guard : d0 pattern = 1) : d398 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5923 (pattern : Twelve) (guard : d1864 pattern = 1) : d406 pattern ≤ (0 : Int) + d315 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d406, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5921 pattern childGuard
    simpa only [d1864, d406, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d406, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5922 pattern childGuard
    simpa only [d1864, d406, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5924 (pattern : Twelve) (guard : d1864 pattern = 1) : d413 pattern ≤ (0 : Int) + d326 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d413, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5918 pattern childGuard
    simpa only [d413, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d413, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5923 pattern childGuard
    simpa only [d413, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5925 (pattern : Twelve) (guard : d1864 pattern = 1) : d412 pattern ≤ (0 : Int) + d327 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d412, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5912 pattern childGuard
    simpa only [d412, d327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d412, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2593 pattern childGuard
    simpa only [d412, d327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5926 (pattern : Twelve) (guard : d1864 pattern = 1) : d417 pattern ≤ (0 : Int) + d335 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d417, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5924 pattern childGuard
    simpa only [d417, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d417, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5925 pattern childGuard
    simpa only [d417, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5927 (pattern : Twelve) (guard : d1864 pattern = 1) : d420 pattern ≤ (0 : Int) + d339 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d420, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5914 pattern childGuard
    simpa only [d420, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d420, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5926 pattern childGuard
    simpa only [d420, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5928 (pattern : Twelve) (guard : d1864 pattern = 1) : d422 pattern ≤ (0 : Int) + d341 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d422, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5899 pattern childGuard
    simpa only [d422, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d422, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5927 pattern childGuard
    simpa only [d422, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5929 (pattern : Twelve) (guard : d1849 pattern = 1) : d380 pattern ≤ (0 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d380, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1849, d380, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d380, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5868 pattern childGuard
    simpa only [d1849, d380, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5930 (pattern : Twelve) (guard : d1863 pattern = 1) : d399 pattern ≤ (0 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d399, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5303 pattern childGuard
    simpa only [d1863, d399, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d399, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5929 pattern childGuard
    simpa only [d1863, d399, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5931 (pattern : Twelve) (guard : d1864 pattern = 1) : d407 pattern ≤ (0 : Int) + d316 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d407, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5930 pattern childGuard
    simpa only [d1864, d407, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d407, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5902 pattern childGuard
    simpa only [d1864, d407, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5932 (pattern : Twelve) (guard : d1864 pattern = 1) : d407 pattern ≤ (0 : Int) + d328 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5903 pattern childGuard
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5931 pattern childGuard
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5933 (pattern : Twelve) (guard : d1864 pattern = 1) : d407 pattern ≤ (0 : Int) + d317 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d407, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5894 pattern childGuard
    simpa only [d1864, d407, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d407, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5902 pattern childGuard
    simpa only [d1864, d407, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5934 (pattern : Twelve) (guard : d1864 pattern = 1) : d407 pattern ≤ (0 : Int) + d329 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5903 pattern childGuard
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5933 pattern childGuard
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5935 (pattern : Twelve) (guard : d1864 pattern = 1) : d407 pattern ≤ (0 : Int) + d336 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5932 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5934 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5936 (pattern : Twelve) (guard : d1849 pattern = 1) : d380 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d380, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1849, d380, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d380, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5884 pattern childGuard
    simpa only [d1849, d380, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5937 (pattern : Twelve) (guard : d1863 pattern = 1) : d399 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d399, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1863, d399, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d399, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5936 pattern childGuard
    simpa only [d1863, d399, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5938 (pattern : Twelve) (guard : d1864 pattern = 1) : d407 pattern ≤ (0 : Int) + d318 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d407, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5937 pattern childGuard
    simpa only [d1864, d407, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d407, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5902 pattern childGuard
    simpa only [d1864, d407, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5939 (pattern : Twelve) (guard : d1864 pattern = 1) : d406 pattern ≤ (0 : Int) + d319 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d406, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5890 pattern childGuard
    simpa only [d1864, d406, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d406, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5922 pattern childGuard
    simpa only [d1864, d406, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5940 (pattern : Twelve) (guard : d1864 pattern = 1) : d413 pattern ≤ (0 : Int) + d330 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d413, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5938 pattern childGuard
    simpa only [d413, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d413, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5939 pattern childGuard
    simpa only [d413, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5941 (pattern : Twelve) (guard : d1864 pattern = 1) : d412 pattern ≤ (0 : Int) + d331 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d412, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5933 pattern childGuard
    simpa only [d412, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d412, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2593 pattern childGuard
    simpa only [d412, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5942 (pattern : Twelve) (guard : d1864 pattern = 1) : d417 pattern ≤ (0 : Int) + d337 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d417, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5940 pattern childGuard
    simpa only [d417, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d417, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5941 pattern childGuard
    simpa only [d417, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5943 (pattern : Twelve) (guard : d1864 pattern = 1) : d420 pattern ≤ (0 : Int) + d340 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d420, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5935 pattern childGuard
    simpa only [d420, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d420, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5942 pattern childGuard
    simpa only [d420, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5944 (pattern : Twelve) (guard : d1864 pattern = 1) : d420 pattern ≤ (0 : Int) + d342 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5943 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5927 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5945 (pattern : Twelve) (guard : d1864 pattern = 1) : d423 pattern ≤ (0 : Int) + d343 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d423, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5928 pattern childGuard
    simpa only [d423, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d423, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5944 pattern childGuard
    simpa only [d423, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5946 (pattern : Twelve) (guard : d0 pattern = 1) : d125 pattern ≤ (0 : Int) + d40 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5947 (pattern : Twelve) (guard : d1849 pattern = 1) : d386 pattern ≤ (0 : Int) + d60 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d386, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5028 pattern childGuard
    simpa only [d1849, d386, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d386, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5946 pattern childGuard
    simpa only [d1849, d386, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5948 (pattern : Twelve) (guard : d1863 pattern = 1) : d400 pattern ≤ (0 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d400, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d1863, d400, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d400, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5947 pattern childGuard
    simpa only [d1863, d400, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5949 (pattern : Twelve) (guard : d0 pattern = 1) : d401 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5950 (pattern : Twelve) (guard : d1864 pattern = 1) : d408 pattern ≤ (0 : Int) + d319 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d408, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5948 pattern childGuard
    simpa only [d1864, d408, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d408, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5949 pattern childGuard
    simpa only [d1864, d408, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5951 (pattern : Twelve) (guard : d1864 pattern = 1) : d414 pattern ≤ (0 : Int) + d330 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d414, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5938 pattern childGuard
    simpa only [d414, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d414, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5950 pattern childGuard
    simpa only [d414, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5952 (pattern : Twelve) (guard : d1864 pattern = 1) : d418 pattern ≤ (0 : Int) + d337 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d418, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5951 pattern childGuard
    simpa only [d418, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d418, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5941 pattern childGuard
    simpa only [d418, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5953 (pattern : Twelve) (guard : d1864 pattern = 1) : d421 pattern ≤ (0 : Int) + d340 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d421, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5935 pattern childGuard
    simpa only [d421, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d421, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5952 pattern childGuard
    simpa only [d421, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5954 (pattern : Twelve) (guard : d0 pattern = 1) : d125 pattern ≤ (0 : Int) + d47 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5955 (pattern : Twelve) (guard : d1849 pattern = 1) : d386 pattern ≤ (0 : Int) + d69 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d386, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5028 pattern childGuard
    simpa only [d1849, d386, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d386, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5954 pattern childGuard
    simpa only [d1849, d386, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5956 (pattern : Twelve) (guard : d1863 pattern = 1) : d400 pattern ≤ (0 : Int) + d89 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d400, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d1863, d400, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d400, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5955 pattern childGuard
    simpa only [d1863, d400, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5957 (pattern : Twelve) (guard : d1864 pattern = 1) : d408 pattern ≤ (0 : Int) + d315 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d408, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5956 pattern childGuard
    simpa only [d1864, d408, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d408, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5949 pattern childGuard
    simpa only [d1864, d408, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5958 (pattern : Twelve) (guard : d1864 pattern = 1) : d414 pattern ≤ (0 : Int) + d326 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d414, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5918 pattern childGuard
    simpa only [d414, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d414, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5957 pattern childGuard
    simpa only [d414, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5959 (pattern : Twelve) (guard : d1864 pattern = 1) : d418 pattern ≤ (0 : Int) + d335 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d418, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5958 pattern childGuard
    simpa only [d418, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d418, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5925 pattern childGuard
    simpa only [d418, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5960 (pattern : Twelve) (guard : d1864 pattern = 1) : d421 pattern ≤ (0 : Int) + d339 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d421, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5914 pattern childGuard
    simpa only [d421, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d421, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5959 pattern childGuard
    simpa only [d421, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5961 (pattern : Twelve) (guard : d1864 pattern = 1) : d421 pattern ≤ (0 : Int) + d342 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5953 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5960 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5962 (pattern : Twelve) (guard : d1864 pattern = 1) : d424 pattern ≤ (0 : Int) + d344 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d424, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5945 pattern childGuard
    simpa only [d424, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d424, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5961 pattern childGuard
    simpa only [d424, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5963 (pattern : Twelve) (guard : d0 pattern = 1) : d818 pattern ≤ (0 : Int) + d816 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5964 (pattern : Twelve) (guard : d1849 pattern = 1) : d1030 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1030, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5088 pattern childGuard
    simpa only [d1849, d1030, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1030, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5963 pattern childGuard
    simpa only [d1849, d1030, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5965 (pattern : Twelve) (guard : d1863 pattern = 1) : d1038 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1038, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5248 pattern childGuard
    simpa only [d1863, d1038, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1038, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5964 pattern childGuard
    simpa only [d1863, d1038, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5966 (pattern : Twelve) (guard : d0 pattern = 1) : d1039 pattern ≤ (0 : Int) + d909 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5967 (pattern : Twelve) (guard : d1864 pattern = 1) : d1048 pattern ≤ (0 : Int) + d980 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1048, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5965 pattern childGuard
    simpa only [d1864, d1048, d980, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1048, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5966 pattern childGuard
    simpa only [d1864, d1048, d980, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5968 (pattern : Twelve) (guard : d1849 pattern = 1) : d1033 pattern ≤ (0 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1033, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d1849, d1033, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1033, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2671 pattern childGuard
    simpa only [d1849, d1033, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5969 (pattern : Twelve) (guard : d1863 pattern = 1) : d1040 pattern ≤ (0 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1040, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5352 pattern childGuard
    simpa only [d1863, d1040, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1040, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5968 pattern childGuard
    simpa only [d1863, d1040, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5970 (pattern : Twelve) (guard : d0 pattern = 1) : d1041 pattern ≤ (0 : Int) + d910 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5971 (pattern : Twelve) (guard : d1864 pattern = 1) : d1049 pattern ≤ (0 : Int) + d981 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1049, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5969 pattern childGuard
    simpa only [d1864, d1049, d981, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1049, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5970 pattern childGuard
    simpa only [d1864, d1049, d981, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5972 (pattern : Twelve) (guard : d1864 pattern = 1) : d1054 pattern ≤ (0 : Int) + d991 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1054, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5967 pattern childGuard
    simpa only [d1054, d991, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1054, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5971 pattern childGuard
    simpa only [d1054, d991, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5973 (pattern : Twelve) (guard : d1849 pattern = 1) : d1033 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1033, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5106 pattern childGuard
    simpa only [d1849, d1033, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1033, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5963 pattern childGuard
    simpa only [d1849, d1033, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5974 (pattern : Twelve) (guard : d1863 pattern = 1) : d1040 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1040, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5265 pattern childGuard
    simpa only [d1863, d1040, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1040, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5973 pattern childGuard
    simpa only [d1863, d1040, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5975 (pattern : Twelve) (guard : d1864 pattern = 1) : d1049 pattern ≤ (0 : Int) + d982 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1049, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5974 pattern childGuard
    simpa only [d1864, d1049, d982, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1049, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5970 pattern childGuard
    simpa only [d1864, d1049, d982, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5976 (pattern : Twelve) (guard : d1863 pattern = 1) : d1042 pattern ≤ (0 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1042, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5271 pattern childGuard
    simpa only [d1863, d1042, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1042, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5968 pattern childGuard
    simpa only [d1863, d1042, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5977 (pattern : Twelve) (guard : d0 pattern = 1) : d1041 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5978 (pattern : Twelve) (guard : d1864 pattern = 1) : d1050 pattern ≤ (0 : Int) + d983 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1050, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5976 pattern childGuard
    simpa only [d1864, d1050, d983, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1050, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5977 pattern childGuard
    simpa only [d1864, d1050, d983, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5979 (pattern : Twelve) (guard : d1864 pattern = 1) : d1055 pattern ≤ (0 : Int) + d992 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1055, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5975 pattern childGuard
    simpa only [d1055, d992, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1055, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5978 pattern childGuard
    simpa only [d1055, d992, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5980 (pattern : Twelve) (guard : d1864 pattern = 1) : d1060 pattern ≤ (0 : Int) + d1000 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1060, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5972 pattern childGuard
    simpa only [d1060, d1000, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1060, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5979 pattern childGuard
    simpa only [d1060, d1000, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5981 (pattern : Twelve) (guard : d0 pattern = 1) : d818 pattern ≤ (0 : Int) + d819 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5982 (pattern : Twelve) (guard : d1849 pattern = 1) : d1033 pattern ≤ (0 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1033, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d1849, d1033, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1033, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5981 pattern childGuard
    simpa only [d1849, d1033, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5983 (pattern : Twelve) (guard : d1863 pattern = 1) : d1043 pattern ≤ (0 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1043, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5280 pattern childGuard
    simpa only [d1863, d1043, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1043, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5982 pattern childGuard
    simpa only [d1863, d1043, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5984 (pattern : Twelve) (guard : d0 pattern = 1) : d1041 pattern ≤ (0 : Int) + d911 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5985 (pattern : Twelve) (guard : d1864 pattern = 1) : d1051 pattern ≤ (0 : Int) + d984 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1051, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5983 pattern childGuard
    simpa only [d1864, d1051, d984, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1051, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5984 pattern childGuard
    simpa only [d1864, d1051, d984, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5986 (pattern : Twelve) (guard : d1849 pattern = 1) : d1034 pattern ≤ (0 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1034, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5034 pattern childGuard
    simpa only [d1849, d1034, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1034, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2692 pattern childGuard
    simpa only [d1849, d1034, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5987 (pattern : Twelve) (guard : d1863 pattern = 1) : d1044 pattern ≤ (0 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1044, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d1863, d1044, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1044, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5986 pattern childGuard
    simpa only [d1863, d1044, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5988 (pattern : Twelve) (guard : d0 pattern = 1) : d1045 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5989 (pattern : Twelve) (guard : d1864 pattern = 1) : d1052 pattern ≤ (0 : Int) + d985 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1052, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5987 pattern childGuard
    simpa only [d1864, d1052, d985, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1052, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5988 pattern childGuard
    simpa only [d1864, d1052, d985, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5990 (pattern : Twelve) (guard : d1864 pattern = 1) : d1056 pattern ≤ (0 : Int) + d993 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1056, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5985 pattern childGuard
    simpa only [d1056, d993, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1056, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5989 pattern childGuard
    simpa only [d1056, d993, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5991 (pattern : Twelve) (guard : d1864 pattern = 1) : d1057 pattern ≤ (0 : Int) + d994 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1057, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5978 pattern childGuard
    simpa only [d1057, d994, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1057, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2593 pattern childGuard
    simpa only [d1057, d994, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5992 (pattern : Twelve) (guard : d1864 pattern = 1) : d1061 pattern ≤ (0 : Int) + d1001 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1061, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5990 pattern childGuard
    simpa only [d1061, d1001, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1061, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5991 pattern childGuard
    simpa only [d1061, d1001, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5993 (pattern : Twelve) (guard : d1864 pattern = 1) : d1064 pattern ≤ (0 : Int) + d1004 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1064, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5980 pattern childGuard
    simpa only [d1064, d1004, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1064, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5992 pattern childGuard
    simpa only [d1064, d1004, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5994 (pattern : Twelve) (guard : d1863 pattern = 1) : d1042 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1042, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5045 pattern childGuard
    simpa only [d1863, d1042, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1042, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5973 pattern childGuard
    simpa only [d1863, d1042, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5995 (pattern : Twelve) (guard : d1864 pattern = 1) : d1050 pattern ≤ (0 : Int) + d986 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1050, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5994 pattern childGuard
    simpa only [d1864, d1050, d986, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1050, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5977 pattern childGuard
    simpa only [d1864, d1050, d986, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5996 (pattern : Twelve) (guard : d0 pattern = 1) : d818 pattern ≤ (0 : Int) + d45 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5997 (pattern : Twelve) (guard : d1849 pattern = 1) : d1033 pattern ≤ (0 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1033, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d1849, d1033, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1033, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5996 pattern childGuard
    simpa only [d1849, d1033, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5998 (pattern : Twelve) (guard : d1863 pattern = 1) : d1042 pattern ≤ (0 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1042, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5271 pattern childGuard
    simpa only [d1863, d1042, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1042, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5997 pattern childGuard
    simpa only [d1863, d1042, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5999 (pattern : Twelve) (guard : d1864 pattern = 1) : d1050 pattern ≤ (0 : Int) + d987 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1050, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5998 pattern childGuard
    simpa only [d1864, d1050, d987, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1050, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5977 pattern childGuard
    simpa only [d1864, d1050, d987, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6000 (pattern : Twelve) (guard : d1864 pattern = 1) : d1050 pattern ≤ (0 : Int) + d995 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5995 pattern childGuard
    simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5999 pattern childGuard
    simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6001 (pattern : Twelve) (guard : d0 pattern = 1) : d818 pattern ≤ (0 : Int) + d46 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6002 (pattern : Twelve) (guard : d1849 pattern = 1) : d1033 pattern ≤ (0 : Int) + d834 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1033, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d1849, d1033, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1033, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6001 pattern childGuard
    simpa only [d1849, d1033, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6003 (pattern : Twelve) (guard : d1863 pattern = 1) : d1042 pattern ≤ (0 : Int) + d849 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1042, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1863, d1042, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1042, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6002 pattern childGuard
    simpa only [d1863, d1042, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6004 (pattern : Twelve) (guard : d1864 pattern = 1) : d1050 pattern ≤ (0 : Int) + d988 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1050, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6003 pattern childGuard
    simpa only [d1864, d1050, d988, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1050, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5977 pattern childGuard
    simpa only [d1864, d1050, d988, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6005 (pattern : Twelve) (guard : d0 pattern = 1) : d820 pattern ≤ (0 : Int) + d47 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6006 (pattern : Twelve) (guard : d1849 pattern = 1) : d1034 pattern ≤ (0 : Int) + d836 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1034, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5034 pattern childGuard
    simpa only [d1849, d1034, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1034, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6005 pattern childGuard
    simpa only [d1849, d1034, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6007 (pattern : Twelve) (guard : d1863 pattern = 1) : d1044 pattern ≤ (0 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1044, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d1863, d1044, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1044, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6006 pattern childGuard
    simpa only [d1863, d1044, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6008 (pattern : Twelve) (guard : d1864 pattern = 1) : d1052 pattern ≤ (0 : Int) + d989 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1052, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6007 pattern childGuard
    simpa only [d1864, d1052, d989, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1052, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5988 pattern childGuard
    simpa only [d1864, d1052, d989, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6009 (pattern : Twelve) (guard : d1864 pattern = 1) : d1058 pattern ≤ (0 : Int) + d996 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1058, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6004 pattern childGuard
    simpa only [d1058, d996, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1058, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6008 pattern childGuard
    simpa only [d1058, d996, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6010 (pattern : Twelve) (guard : d1864 pattern = 1) : d1057 pattern ≤ (0 : Int) + d997 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1057, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5999 pattern childGuard
    simpa only [d1057, d997, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1057, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2593 pattern childGuard
    simpa only [d1057, d997, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6011 (pattern : Twelve) (guard : d1864 pattern = 1) : d1062 pattern ≤ (0 : Int) + d1002 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1062, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6009 pattern childGuard
    simpa only [d1062, d1002, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1062, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6010 pattern childGuard
    simpa only [d1062, d1002, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6012 (pattern : Twelve) (guard : d1864 pattern = 1) : d1065 pattern ≤ (0 : Int) + d1005 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1065, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6000 pattern childGuard
    simpa only [d1065, d1005, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1065, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6011 pattern childGuard
    simpa only [d1065, d1005, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6013 (pattern : Twelve) (guard : d1864 pattern = 1) : d1067 pattern ≤ (0 : Int) + d1007 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1067, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5993 pattern childGuard
    simpa only [d1067, d1007, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1067, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6012 pattern childGuard
    simpa only [d1067, d1007, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6014 (pattern : Twelve) (guard : d1864 pattern = 1) : d1050 pattern ≤ (0 : Int) + d998 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5995 pattern childGuard
    simpa only [d998, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5978 pattern childGuard
    simpa only [d998, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6015 (pattern : Twelve) (guard : d1863 pattern = 1) : d1042 pattern ≤ (0 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1042, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1863, d1042, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1042, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5982 pattern childGuard
    simpa only [d1863, d1042, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6016 (pattern : Twelve) (guard : d1864 pattern = 1) : d1050 pattern ≤ (0 : Int) + d990 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1050, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6015 pattern childGuard
    simpa only [d1864, d1050, d990, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1050, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5977 pattern childGuard
    simpa only [d1864, d1050, d990, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6017 (pattern : Twelve) (guard : d1864 pattern = 1) : d1058 pattern ≤ (0 : Int) + d999 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1058, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6016 pattern childGuard
    simpa only [d1058, d999, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1058, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5989 pattern childGuard
    simpa only [d1058, d999, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6018 (pattern : Twelve) (guard : d1864 pattern = 1) : d1062 pattern ≤ (0 : Int) + d1003 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1062, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6017 pattern childGuard
    simpa only [d1062, d1003, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1062, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5991 pattern childGuard
    simpa only [d1062, d1003, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6019 (pattern : Twelve) (guard : d1864 pattern = 1) : d1065 pattern ≤ (0 : Int) + d1006 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1065, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6014 pattern childGuard
    simpa only [d1065, d1006, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1065, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6018 pattern childGuard
    simpa only [d1065, d1006, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
