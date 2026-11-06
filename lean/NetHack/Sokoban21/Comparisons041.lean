/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons040
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c5740 (pattern : Twelve) (guard : d1869 pattern = 1) : d415 pattern ≤ (0 : Int) + d358 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d415, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5737 pattern childGuard
    simpa only [d415, d358, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d415, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5739 pattern childGuard
    simpa only [d415, d358, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5741 (pattern : Twelve) (guard : d0 pattern = 1) : d169 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5742 (pattern : Twelve) (guard : d1848 pattern = 1) : d370 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d370, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5741 pattern childGuard
    simpa only [d1848, d370, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5743 (pattern : Twelve) (guard : d0 pattern = 1) : d170 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5744 (pattern : Twelve) (guard : d1848 pattern = 1) : d371 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d371, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5743 pattern childGuard
    simpa only [d1848, d371, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5745 (pattern : Twelve) (guard : d1848 pattern = 1) : d381 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5742 pattern childGuard
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5744 pattern childGuard
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5746 (pattern : Twelve) (guard : d0 pattern = 1) : d170 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5747 (pattern : Twelve) (guard : d1848 pattern = 1) : d371 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d371, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d371, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d371, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5746 pattern childGuard
    simpa only [d1848, d371, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5748 (pattern : Twelve) (guard : d1848 pattern = 1) : d382 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d382, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5747 pattern childGuard
    simpa only [d382, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d382, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5106 pattern childGuard
    simpa only [d382, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5749 (pattern : Twelve) (guard : d1848 pattern = 1) : d395 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d395, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5745 pattern childGuard
    simpa only [d395, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d395, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5748 pattern childGuard
    simpa only [d395, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5750 (pattern : Twelve) (guard : d1848 pattern = 1) : d383 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5744 pattern childGuard
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5045 pattern childGuard
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5751 (pattern : Twelve) (guard : d1848 pattern = 1) : d396 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d396, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5750 pattern childGuard
    simpa only [d396, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d396, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5519 pattern childGuard
    simpa only [d396, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5752 (pattern : Twelve) (guard : d1848 pattern = 1) : d405 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d405, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5749 pattern childGuard
    simpa only [d405, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d405, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5751 pattern childGuard
    simpa only [d405, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5753 (pattern : Twelve) (guard : d0 pattern = 1) : d406 pattern ≤ (0 : Int) + d211 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5754 (pattern : Twelve) (guard : d1869 pattern = 1) : d411 pattern ≤ (0 : Int) + d354 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d411, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5752 pattern childGuard
    simpa only [d1869, d411, d354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d411, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5753 pattern childGuard
    simpa only [d1869, d411, d354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5755 (pattern : Twelve) (guard : d1869 pattern = 1) : d412 pattern ≤ (0 : Int) + d355 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d412, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5528 pattern childGuard
    simpa only [d1869, d412, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d412, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d412, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5756 (pattern : Twelve) (guard : d1869 pattern = 1) : d416 pattern ≤ (0 : Int) + d359 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d416, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5754 pattern childGuard
    simpa only [d416, d359, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d416, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5755 pattern childGuard
    simpa only [d416, d359, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5757 (pattern : Twelve) (guard : d1869 pattern = 1) : d419 pattern ≤ (0 : Int) + d361 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d419, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5740 pattern childGuard
    simpa only [d419, d361, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d419, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5756 pattern childGuard
    simpa only [d419, d361, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5758 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5518 pattern childGuard
    simpa only [d407, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5533 pattern childGuard
    simpa only [d407, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5759 (pattern : Twelve) (guard : d0 pattern = 1) : d407 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5760 (pattern : Twelve) (guard : d1869 pattern = 1) : d407 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5758 pattern childGuard
    simpa only [d1869, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5759 pattern childGuard
    simpa only [d1869, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5761 (pattern : Twelve) (guard : d0 pattern = 1) : d406 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5762 (pattern : Twelve) (guard : d1869 pattern = 1) : d413 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d413, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5758 pattern childGuard
    simpa only [d1869, d413, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d413, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5761 pattern childGuard
    simpa only [d1869, d413, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5763 (pattern : Twelve) (guard : d1869 pattern = 1) : d412 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d412, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5758 pattern childGuard
    simpa only [d1869, d412, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d412, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d412, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5764 (pattern : Twelve) (guard : d1869 pattern = 1) : d417 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5762 pattern childGuard
    simpa only [d417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5763 pattern childGuard
    simpa only [d417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5765 (pattern : Twelve) (guard : d1869 pattern = 1) : d420 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5760 pattern childGuard
    simpa only [d420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5764 pattern childGuard
    simpa only [d420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5766 (pattern : Twelve) (guard : d1869 pattern = 1) : d422 pattern ≤ (0 : Int) + d362 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d422, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5757 pattern childGuard
    simpa only [d422, d362, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d422, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5765 pattern childGuard
    simpa only [d422, d362, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5767 (pattern : Twelve) (guard : d1869 pattern = 1) : d407 pattern ≤ (0 : Int) + d357 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5521 pattern childGuard
    simpa only [d1869, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5759 pattern childGuard
    simpa only [d1869, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5768 (pattern : Twelve) (guard : d1869 pattern = 1) : d407 pattern ≤ (0 : Int) + d355 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5528 pattern childGuard
    simpa only [d1869, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5759 pattern childGuard
    simpa only [d1869, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5769 (pattern : Twelve) (guard : d1869 pattern = 1) : d407 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5767 pattern childGuard
    simpa only [d360, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5768 pattern childGuard
    simpa only [d360, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5770 (pattern : Twelve) (guard : d1869 pattern = 1) : d413 pattern ≤ (0 : Int) + d357 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d413, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5521 pattern childGuard
    simpa only [d1869, d413, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d413, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5761 pattern childGuard
    simpa only [d1869, d413, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5771 (pattern : Twelve) (guard : d1869 pattern = 1) : d417 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d417, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5770 pattern childGuard
    simpa only [d417, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d417, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5755 pattern childGuard
    simpa only [d417, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5772 (pattern : Twelve) (guard : d1869 pattern = 1) : d420 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5769 pattern childGuard
    simpa only [d420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5771 pattern childGuard
    simpa only [d420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5773 (pattern : Twelve) (guard : d1869 pattern = 1) : d420 pattern ≤ (0 : Int) + d363 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5772 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5765 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5774 (pattern : Twelve) (guard : d1869 pattern = 1) : d423 pattern ≤ (0 : Int) + d364 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d423, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5766 pattern childGuard
    simpa only [d423, d364, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d423, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5773 pattern childGuard
    simpa only [d423, d364, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5775 (pattern : Twelve) (guard : d0 pattern = 1) : d408 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5776 (pattern : Twelve) (guard : d1869 pattern = 1) : d414 pattern ≤ (0 : Int) + d357 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d414, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5521 pattern childGuard
    simpa only [d1869, d414, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d414, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5775 pattern childGuard
    simpa only [d1869, d414, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5777 (pattern : Twelve) (guard : d1869 pattern = 1) : d418 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d418, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5776 pattern childGuard
    simpa only [d418, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d418, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5755 pattern childGuard
    simpa only [d418, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5778 (pattern : Twelve) (guard : d1869 pattern = 1) : d421 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5769 pattern childGuard
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5777 pattern childGuard
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5779 (pattern : Twelve) (guard : d1869 pattern = 1) : d414 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d414, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5758 pattern childGuard
    simpa only [d1869, d414, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d414, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5775 pattern childGuard
    simpa only [d1869, d414, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5780 (pattern : Twelve) (guard : d1869 pattern = 1) : d418 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5779 pattern childGuard
    simpa only [d418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5763 pattern childGuard
    simpa only [d418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5781 (pattern : Twelve) (guard : d1869 pattern = 1) : d421 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5760 pattern childGuard
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5780 pattern childGuard
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5782 (pattern : Twelve) (guard : d1869 pattern = 1) : d421 pattern ≤ (0 : Int) + d363 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5778 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5781 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5783 (pattern : Twelve) (guard : d1869 pattern = 1) : d424 pattern ≤ (0 : Int) + d365 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d424, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5774 pattern childGuard
    simpa only [d424, d365, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d424, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5782 pattern childGuard
    simpa only [d424, d365, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5784 (pattern : Twelve) (guard : d0 pattern = 1) : d1049 pattern ≤ (0 : Int) + d913 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5785 (pattern : Twelve) (guard : d1869 pattern = 1) : d1054 pattern ≤ (0 : Int) + d1018 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1054, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5576 pattern childGuard
    simpa only [d1869, d1054, d1018, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1054, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5784 pattern childGuard
    simpa only [d1869, d1054, d1018, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5786 (pattern : Twelve) (guard : d0 pattern = 1) : d1050 pattern ≤ (0 : Int) + d914 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5787 (pattern : Twelve) (guard : d1869 pattern = 1) : d1055 pattern ≤ (0 : Int) + d1019 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1055, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5586 pattern childGuard
    simpa only [d1869, d1055, d1019, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1055, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5786 pattern childGuard
    simpa only [d1869, d1055, d1019, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5788 (pattern : Twelve) (guard : d1869 pattern = 1) : d1060 pattern ≤ (0 : Int) + d1023 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1060, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5785 pattern childGuard
    simpa only [d1060, d1023, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1060, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5787 pattern childGuard
    simpa only [d1060, d1023, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5789 (pattern : Twelve) (guard : d1848 pattern = 1) : d1043 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1043, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5750 pattern childGuard
    simpa only [d1043, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1043, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5583 pattern childGuard
    simpa only [d1043, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5790 (pattern : Twelve) (guard : d1848 pattern = 1) : d1051 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1051, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5789 pattern childGuard
    simpa only [d1051, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1051, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5585 pattern childGuard
    simpa only [d1051, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5791 (pattern : Twelve) (guard : d0 pattern = 1) : d1052 pattern ≤ (0 : Int) + d916 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5792 (pattern : Twelve) (guard : d1869 pattern = 1) : d1056 pattern ≤ (0 : Int) + d1020 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1056, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5790 pattern childGuard
    simpa only [d1869, d1056, d1020, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1056, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5791 pattern childGuard
    simpa only [d1869, d1056, d1020, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5793 (pattern : Twelve) (guard : d1869 pattern = 1) : d1057 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1057, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5607 pattern childGuard
    simpa only [d1869, d1057, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1057, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1057, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5794 (pattern : Twelve) (guard : d1869 pattern = 1) : d1061 pattern ≤ (0 : Int) + d1024 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1061, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5792 pattern childGuard
    simpa only [d1061, d1024, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1061, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5793 pattern childGuard
    simpa only [d1061, d1024, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5795 (pattern : Twelve) (guard : d1869 pattern = 1) : d1064 pattern ≤ (0 : Int) + d1025 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1064, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5788 pattern childGuard
    simpa only [d1064, d1025, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1064, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5794 pattern childGuard
    simpa only [d1064, d1025, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5796 (pattern : Twelve) (guard : d1848 pattern = 1) : d1041 pattern ≤ (0 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5132 pattern childGuard
    simpa only [d1041, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5574 pattern childGuard
    simpa only [d1041, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5797 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (0 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5606 pattern childGuard
    simpa only [d1050, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5796 pattern childGuard
    simpa only [d1050, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5798 (pattern : Twelve) (guard : d0 pattern = 1) : d1050 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5799 (pattern : Twelve) (guard : d1869 pattern = 1) : d1050 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5797 pattern childGuard
    simpa only [d1869, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5798 pattern childGuard
    simpa only [d1869, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5800 (pattern : Twelve) (guard : d0 pattern = 1) : d1052 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5801 (pattern : Twelve) (guard : d1869 pattern = 1) : d1058 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1058, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5797 pattern childGuard
    simpa only [d1869, d1058, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1058, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5800 pattern childGuard
    simpa only [d1869, d1058, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5802 (pattern : Twelve) (guard : d1869 pattern = 1) : d1057 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1057, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5797 pattern childGuard
    simpa only [d1869, d1057, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1057, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1057, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5803 (pattern : Twelve) (guard : d1869 pattern = 1) : d1062 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5801 pattern childGuard
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5802 pattern childGuard
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5804 (pattern : Twelve) (guard : d1869 pattern = 1) : d1065 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5799 pattern childGuard
    simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5803 pattern childGuard
    simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5805 (pattern : Twelve) (guard : d1869 pattern = 1) : d1067 pattern ≤ (0 : Int) + d1026 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1067, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5795 pattern childGuard
    simpa only [d1067, d1026, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1067, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5804 pattern childGuard
    simpa only [d1067, d1026, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5806 (pattern : Twelve) (guard : d1869 pattern = 1) : d1050 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5607 pattern childGuard
    simpa only [d1869, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5798 pattern childGuard
    simpa only [d1869, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5807 (pattern : Twelve) (guard : d1869 pattern = 1) : d1058 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1058, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5607 pattern childGuard
    simpa only [d1869, d1058, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1058, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5800 pattern childGuard
    simpa only [d1869, d1058, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5808 (pattern : Twelve) (guard : d1869 pattern = 1) : d1062 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5807 pattern childGuard
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5793 pattern childGuard
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5809 (pattern : Twelve) (guard : d1869 pattern = 1) : d1065 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5806 pattern childGuard
    simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5808 pattern childGuard
    simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5810 (pattern : Twelve) (guard : d1869 pattern = 1) : d1065 pattern ≤ (0 : Int) + d1027 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5809 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5804 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5811 (pattern : Twelve) (guard : d1869 pattern = 1) : d1068 pattern ≤ (0 : Int) + d1028 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1068, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5805 pattern childGuard
    simpa only [d1068, d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1068, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5810 pattern childGuard
    simpa only [d1068, d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5812 (pattern : Twelve) (guard : d0 pattern = 1) : d1053 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5813 (pattern : Twelve) (guard : d1869 pattern = 1) : d1059 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1059, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5607 pattern childGuard
    simpa only [d1869, d1059, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1059, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5812 pattern childGuard
    simpa only [d1869, d1059, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5814 (pattern : Twelve) (guard : d1869 pattern = 1) : d1063 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5813 pattern childGuard
    simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5793 pattern childGuard
    simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5815 (pattern : Twelve) (guard : d1869 pattern = 1) : d1066 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5806 pattern childGuard
    simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5814 pattern childGuard
    simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5816 (pattern : Twelve) (guard : d1869 pattern = 1) : d1059 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1059, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5797 pattern childGuard
    simpa only [d1869, d1059, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1059, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5812 pattern childGuard
    simpa only [d1869, d1059, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5817 (pattern : Twelve) (guard : d1869 pattern = 1) : d1063 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5816 pattern childGuard
    simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5802 pattern childGuard
    simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5818 (pattern : Twelve) (guard : d1869 pattern = 1) : d1066 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5799 pattern childGuard
    simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5817 pattern childGuard
    simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5819 (pattern : Twelve) (guard : d1869 pattern = 1) : d1066 pattern ≤ (0 : Int) + d1027 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5815 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5818 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5820 (pattern : Twelve) (guard : d1869 pattern = 1) : d1069 pattern ≤ (0 : Int) + d1029 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1069, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5811 pattern childGuard
    simpa only [d1069, d1029, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1069, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5819 pattern childGuard
    simpa only [d1069, d1029, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5821 (pattern : Twelve) (guard : d0 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1357 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5822 (pattern : Twelve) (guard : d1869 pattern = 1) : d1459 pattern ≤ (0 : Int) + d1435 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1459, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5651 pattern childGuard
    simpa only [d1869, d1459, d1435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1459, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5821 pattern childGuard
    simpa only [d1869, d1459, d1435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5823 (pattern : Twelve) (guard : d0 pattern = 1) : d1456 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5824 (pattern : Twelve) (guard : d1869 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5659 pattern childGuard
    simpa only [d1869, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5823 pattern childGuard
    simpa only [d1869, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5825 (pattern : Twelve) (guard : d1869 pattern = 1) : d1463 pattern ≤ (0 : Int) + d1438 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1463, d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5822 pattern childGuard
    simpa only [d1463, d1438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1463, d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5824 pattern childGuard
    simpa only [d1463, d1438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5826 (pattern : Twelve) (guard : d0 pattern = 1) : d1457 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5827 (pattern : Twelve) (guard : d1869 pattern = 1) : d1460 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1460, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5659 pattern childGuard
    simpa only [d1869, d1460, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1460, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5826 pattern childGuard
    simpa only [d1869, d1460, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5828 (pattern : Twelve) (guard : d1869 pattern = 1) : d1461 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1461, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5659 pattern childGuard
    simpa only [d1869, d1461, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1461, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1461, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5829 (pattern : Twelve) (guard : d1869 pattern = 1) : d1464 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5827 pattern childGuard
    simpa only [d1464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5828 pattern childGuard
    simpa only [d1464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5830 (pattern : Twelve) (guard : d1869 pattern = 1) : d1466 pattern ≤ (0 : Int) + d1439 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1466, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5825 pattern childGuard
    simpa only [d1466, d1439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1466, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5829 pattern childGuard
    simpa only [d1466, d1439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5831 (pattern : Twelve) (guard : d1848 pattern = 1) : d1449 pattern ≤ (0 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5189 pattern childGuard
    simpa only [d1449, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1449, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5832 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5658 pattern childGuard
    simpa only [d1456, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5831 pattern childGuard
    simpa only [d1456, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5833 (pattern : Twelve) (guard : d1869 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5832 pattern childGuard
    simpa only [d1869, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5823 pattern childGuard
    simpa only [d1869, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5834 (pattern : Twelve) (guard : d1869 pattern = 1) : d1460 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1460, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5832 pattern childGuard
    simpa only [d1869, d1460, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1460, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5826 pattern childGuard
    simpa only [d1869, d1460, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5835 (pattern : Twelve) (guard : d1869 pattern = 1) : d1461 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1461, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5832 pattern childGuard
    simpa only [d1869, d1461, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1461, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1461, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5836 (pattern : Twelve) (guard : d1869 pattern = 1) : d1464 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5834 pattern childGuard
    simpa only [d1464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5835 pattern childGuard
    simpa only [d1464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5837 (pattern : Twelve) (guard : d1869 pattern = 1) : d1467 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5833 pattern childGuard
    simpa only [d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5836 pattern childGuard
    simpa only [d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5838 (pattern : Twelve) (guard : d1869 pattern = 1) : d1469 pattern ≤ (0 : Int) + d1440 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1469, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5830 pattern childGuard
    simpa only [d1469, d1440, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1469, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5837 pattern childGuard
    simpa only [d1469, d1440, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5839 (pattern : Twelve) (guard : d1869 pattern = 1) : d1467 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5824 pattern childGuard
    simpa only [d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5829 pattern childGuard
    simpa only [d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5840 (pattern : Twelve) (guard : d1869 pattern = 1) : d1467 pattern ≤ (0 : Int) + d1441 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5839 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5837 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5841 (pattern : Twelve) (guard : d1869 pattern = 1) : d1470 pattern ≤ (0 : Int) + d1442 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1470, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5838 pattern childGuard
    simpa only [d1470, d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1470, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5840 pattern childGuard
    simpa only [d1470, d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5842 (pattern : Twelve) (guard : d0 pattern = 1) : d1458 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5843 (pattern : Twelve) (guard : d1869 pattern = 1) : d1462 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1462, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5659 pattern childGuard
    simpa only [d1869, d1462, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1462, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5842 pattern childGuard
    simpa only [d1869, d1462, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5844 (pattern : Twelve) (guard : d1869 pattern = 1) : d1465 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5843 pattern childGuard
    simpa only [d1465, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5828 pattern childGuard
    simpa only [d1465, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5845 (pattern : Twelve) (guard : d1869 pattern = 1) : d1468 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5824 pattern childGuard
    simpa only [d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5844 pattern childGuard
    simpa only [d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5846 (pattern : Twelve) (guard : d1869 pattern = 1) : d1462 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1462, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5832 pattern childGuard
    simpa only [d1869, d1462, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1462, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5842 pattern childGuard
    simpa only [d1869, d1462, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5847 (pattern : Twelve) (guard : d1869 pattern = 1) : d1465 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5846 pattern childGuard
    simpa only [d1465, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5835 pattern childGuard
    simpa only [d1465, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5848 (pattern : Twelve) (guard : d1869 pattern = 1) : d1468 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5833 pattern childGuard
    simpa only [d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5847 pattern childGuard
    simpa only [d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5849 (pattern : Twelve) (guard : d1869 pattern = 1) : d1468 pattern ≤ (0 : Int) + d1441 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5845 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5848 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5850 (pattern : Twelve) (guard : d1869 pattern = 1) : d1471 pattern ≤ (0 : Int) + d1443 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1471, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5841 pattern childGuard
    simpa only [d1471, d1443, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1471, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5849 pattern childGuard
    simpa only [d1471, d1443, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5851 (pattern : Twelve) (guard : d0 pattern = 1) : d1719 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5852 (pattern : Twelve) (guard : d1869 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5704 pattern childGuard
    simpa only [d1869, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5851 pattern childGuard
    simpa only [d1869, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5853 (pattern : Twelve) (guard : d0 pattern = 1) : d1720 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5854 (pattern : Twelve) (guard : d1869 pattern = 1) : d1722 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1722, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5704 pattern childGuard
    simpa only [d1869, d1722, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1722, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5853 pattern childGuard
    simpa only [d1869, d1722, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5855 (pattern : Twelve) (guard : d1869 pattern = 1) : d1723 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1723, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5704 pattern childGuard
    simpa only [d1869, d1723, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1723, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1723, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5856 (pattern : Twelve) (guard : d1869 pattern = 1) : d1725 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5854 pattern childGuard
    simpa only [d1725, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5855 pattern childGuard
    simpa only [d1725, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5857 (pattern : Twelve) (guard : d1869 pattern = 1) : d1727 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5852 pattern childGuard
    simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5856 pattern childGuard
    simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5858 (pattern : Twelve) (guard : d0 pattern = 1) : d1721 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5859 (pattern : Twelve) (guard : d1869 pattern = 1) : d1724 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1724, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5704 pattern childGuard
    simpa only [d1869, d1724, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1724, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5858 pattern childGuard
    simpa only [d1869, d1724, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5860 (pattern : Twelve) (guard : d1869 pattern = 1) : d1726 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5859 pattern childGuard
    simpa only [d1726, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5855 pattern childGuard
    simpa only [d1726, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5861 (pattern : Twelve) (guard : d1869 pattern = 1) : d1728 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5852 pattern childGuard
    simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5860 pattern childGuard
    simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5862 (pattern : Twelve) (guard : d1869 pattern = 1) : d1729 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5857 pattern childGuard
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5861 pattern childGuard
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5863 (pattern : Twelve) (guard : d0 pattern = 1) : d366 pattern ≤ (0 : Int) + d27 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5864 (pattern : Twelve) (guard : d1849 pattern = 1) : d372 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d372, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4961 pattern childGuard
    simpa only [d1849, d372, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d372, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5863 pattern childGuard
    simpa only [d1849, d372, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5865 (pattern : Twelve) (guard : d1863 pattern = 1) : d389 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d389, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5243 pattern childGuard
    simpa only [d1863, d389, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d389, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5864 pattern childGuard
    simpa only [d1863, d389, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5866 (pattern : Twelve) (guard : d0 pattern = 1) : d390 pattern ≤ (0 : Int) + d198 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5867 (pattern : Twelve) (guard : d1864 pattern = 1) : d402 pattern ≤ (0 : Int) + d304 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d402, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5865 pattern childGuard
    simpa only [d1864, d402, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d402, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5866 pattern childGuard
    simpa only [d1864, d402, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5868 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d32 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5869 (pattern : Twelve) (guard : d1849 pattern = 1) : d376 pattern ≤ (0 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d376, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4979 pattern childGuard
    simpa only [d1849, d376, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d376, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5868 pattern childGuard
    simpa only [d1849, d376, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5870 (pattern : Twelve) (guard : d1863 pattern = 1) : d391 pattern ≤ (0 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d391, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5254 pattern childGuard
    simpa only [d1863, d391, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d391, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5869 pattern childGuard
    simpa only [d1863, d391, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5871 (pattern : Twelve) (guard : d0 pattern = 1) : d392 pattern ≤ (0 : Int) + d200 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5872 (pattern : Twelve) (guard : d1864 pattern = 1) : d403 pattern ≤ (0 : Int) + d305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d403, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5870 pattern childGuard
    simpa only [d1864, d403, d305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d403, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5871 pattern childGuard
    simpa only [d1864, d403, d305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5873 (pattern : Twelve) (guard : d1864 pattern = 1) : d409 pattern ≤ (0 : Int) + d320 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d409, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5867 pattern childGuard
    simpa only [d409, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d409, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5872 pattern childGuard
    simpa only [d409, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5874 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d27 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5875 (pattern : Twelve) (guard : d1849 pattern = 1) : d376 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d376, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4994 pattern childGuard
    simpa only [d1849, d376, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d376, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5874 pattern childGuard
    simpa only [d1849, d376, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5876 (pattern : Twelve) (guard : d1863 pattern = 1) : d391 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d391, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5263 pattern childGuard
    simpa only [d1863, d391, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d391, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5875 pattern childGuard
    simpa only [d1863, d391, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5877 (pattern : Twelve) (guard : d1864 pattern = 1) : d403 pattern ≤ (0 : Int) + d306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d403, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5876 pattern childGuard
    simpa only [d1864, d403, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d403, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5871 pattern childGuard
    simpa only [d1864, d403, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5878 (pattern : Twelve) (guard : d1849 pattern = 1) : d380 pattern ≤ (0 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d380, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1849, d380, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d380, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2568 pattern childGuard
    simpa only [d1849, d380, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5879 (pattern : Twelve) (guard : d1863 pattern = 1) : d393 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d393, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5268 pattern childGuard
    simpa only [d1863, d393, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d393, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5878 pattern childGuard
    simpa only [d1863, d393, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
