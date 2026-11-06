/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons033
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c4760 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1022, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4759 pattern childGuard
    simpa only [d1869, d1022, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1022, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4736 pattern childGuard
    simpa only [d1869, d1022, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4761 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d119 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4762 (pattern : Twelve) (guard : d1848 pattern = 1) : d823 pattern ≤ (0 : Int) + d879 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d823, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d823, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d823, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4761 pattern childGuard
    simpa only [d1848, d823, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4763 (pattern : Twelve) (guard : d1848 pattern = 1) : d823 pattern ≤ (0 : Int) + d886 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4503 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4762 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4764 (pattern : Twelve) (guard : d1848 pattern = 1) : d846 pattern ≤ (0 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d846, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4763 pattern childGuard
    simpa only [d846, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d846, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4733 pattern childGuard
    simpa only [d846, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4765 (pattern : Twelve) (guard : d1848 pattern = 1) : d857 pattern ≤ (0 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d857, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4743 pattern childGuard
    simpa only [d857, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d857, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4764 pattern childGuard
    simpa only [d857, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4766 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1022, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4765 pattern childGuard
    simpa only [d1869, d1022, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1022, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4749 pattern childGuard
    simpa only [d1869, d1022, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4767 (pattern : Twelve) (guard : d1848 pattern = 1) : d846 pattern ≤ (0 : Int) + d893 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d846, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4714 pattern childGuard
    simpa only [d846, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d846, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4733 pattern childGuard
    simpa only [d846, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4768 (pattern : Twelve) (guard : d1848 pattern = 1) : d857 pattern ≤ (0 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d857, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4752 pattern childGuard
    simpa only [d857, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d857, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4767 pattern childGuard
    simpa only [d857, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4769 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1022, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4768 pattern childGuard
    simpa only [d1869, d1022, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1022, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1022, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4770 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4766 pattern childGuard
    simpa only [d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4769 pattern childGuard
    simpa only [d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4771 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4760 pattern childGuard
    simpa only [d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4770 pattern childGuard
    simpa only [d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4772 (pattern : Twelve) (guard : d1869 pattern = 1) : d1027 pattern ≤ (0 : Int) + d906 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4757 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4771 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4773 (pattern : Twelve) (guard : d1869 pattern = 1) : d1029 pattern ≤ (0 : Int) + d907 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1029, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4726 pattern childGuard
    simpa only [d1029, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1029, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4772 pattern childGuard
    simpa only [d1029, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4774 (pattern : Twelve) (guard : d1848 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1305 pattern := by
  omega
theorem c4775 (pattern : Twelve) (guard : d1869 pattern = 1) : d1435 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1435, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4774 pattern childGuard
    simpa only [d1869, d1435, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1435, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4363 pattern childGuard
    simpa only [d1869, d1435, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4776 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1436, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4774 pattern childGuard
    simpa only [d1869, d1436, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1436, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4365 pattern childGuard
    simpa only [d1869, d1436, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4777 (pattern : Twelve) (guard : d1869 pattern = 1) : d1438 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4775 pattern childGuard
    simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4776 pattern childGuard
    simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4778 (pattern : Twelve) (guard : d0 pattern = 1) : d872 pattern ≤ (0 : Int) + d119 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4779 (pattern : Twelve) (guard : d1848 pattern = 1) : d872 pattern ≤ (0 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4265 pattern childGuard
    simpa only [d1848, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4778 pattern childGuard
    simpa only [d1848, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4780 (pattern : Twelve) (guard : d1848 pattern = 1) : d1284 pattern ≤ (0 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1284, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4534 pattern childGuard
    simpa only [d1284, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1284, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4779 pattern childGuard
    simpa only [d1284, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4781 (pattern : Twelve) (guard : d1848 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1293, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4485 pattern childGuard
    simpa only [d1293, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1293, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4780 pattern childGuard
    simpa only [d1293, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4782 (pattern : Twelve) (guard : d1848 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1294, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4538 pattern childGuard
    simpa only [d1294, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1294, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1294, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4783 (pattern : Twelve) (guard : d1848 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4781 pattern childGuard
    simpa only [d1305, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4782 pattern childGuard
    simpa only [d1305, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4784 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1308 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4785 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1436, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4783 pattern childGuard
    simpa only [d1869, d1436, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1436, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4784 pattern childGuard
    simpa only [d1869, d1436, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4786 (pattern : Twelve) (guard : d1848 pattern = 1) : d1284 pattern ≤ (0 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1284, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4534 pattern childGuard
    simpa only [d1284, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1284, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4266 pattern childGuard
    simpa only [d1284, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4787 (pattern : Twelve) (guard : d1848 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1293, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4700 pattern childGuard
    simpa only [d1293, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1293, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4786 pattern childGuard
    simpa only [d1293, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4788 (pattern : Twelve) (guard : d1848 pattern = 1) : d19 pattern ≤ (0 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4538 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1473 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4789 (pattern : Twelve) (guard : d1848 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1294, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4788 pattern childGuard
    simpa only [d1294, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1294, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1294, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4790 (pattern : Twelve) (guard : d1848 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4787 pattern childGuard
    simpa only [d1305, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4789 pattern childGuard
    simpa only [d1305, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4791 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1436, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4790 pattern childGuard
    simpa only [d1869, d1436, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1436, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1436, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4792 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4785 pattern childGuard
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4791 pattern childGuard
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4793 (pattern : Twelve) (guard : d1869 pattern = 1) : d1439 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1439, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4777 pattern childGuard
    simpa only [d1439, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1439, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4792 pattern childGuard
    simpa only [d1439, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4794 (pattern : Twelve) (guard : d1848 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1293 pattern := by
  omega
theorem c4795 (pattern : Twelve) (guard : d1848 pattern = 1) : d1301 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1301, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1772 pattern childGuard
    simpa only [d1301, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1301, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1301, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4796 (pattern : Twelve) (guard : d1848 pattern = 1) : d1309 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1309, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4794 pattern childGuard
    simpa only [d1309, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1309, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4795 pattern childGuard
    simpa only [d1309, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4797 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1437, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4796 pattern childGuard
    simpa only [d1869, d1437, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1437, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4365 pattern childGuard
    simpa only [d1869, d1437, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4798 (pattern : Twelve) (guard : d1848 pattern = 1) : d1301 pattern ≤ (0 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1301, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4552 pattern childGuard
    simpa only [d1301, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1301, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1301, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4799 (pattern : Twelve) (guard : d1848 pattern = 1) : d1309 pattern ≤ (0 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1309, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4781 pattern childGuard
    simpa only [d1309, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1309, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4798 pattern childGuard
    simpa only [d1309, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4800 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1437, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4799 pattern childGuard
    simpa only [d1869, d1437, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1437, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4784 pattern childGuard
    simpa only [d1869, d1437, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4801 (pattern : Twelve) (guard : d1848 pattern = 1) : d1283 pattern ≤ (0 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4552 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1501 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4802 (pattern : Twelve) (guard : d1848 pattern = 1) : d1301 pattern ≤ (0 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1301, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4801 pattern childGuard
    simpa only [d1301, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1301, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1301, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4803 (pattern : Twelve) (guard : d1848 pattern = 1) : d1309 pattern ≤ (0 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1309, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4787 pattern childGuard
    simpa only [d1309, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1309, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4802 pattern childGuard
    simpa only [d1309, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4804 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1437, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4803 pattern childGuard
    simpa only [d1869, d1437, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1437, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1437, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4805 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4800 pattern childGuard
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4804 pattern childGuard
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4806 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4797 pattern childGuard
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4805 pattern childGuard
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4807 (pattern : Twelve) (guard : d1869 pattern = 1) : d1440 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4793 pattern childGuard
    simpa only [d1440, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4806 pattern childGuard
    simpa only [d1440, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4808 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4776 pattern childGuard
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4792 pattern childGuard
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4809 (pattern : Twelve) (guard : d1869 pattern = 1) : d1441 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4808 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4806 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4810 (pattern : Twelve) (guard : d1869 pattern = 1) : d1442 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4807 pattern childGuard
    simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4809 pattern childGuard
    simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4811 (pattern : Twelve) (guard : d0 pattern = 1) : d872 pattern ≤ (0 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4812 (pattern : Twelve) (guard : d1848 pattern = 1) : d1278 pattern ≤ (0 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1278, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1469 pattern childGuard
    simpa only [d1848, d1278, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1278, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4811 pattern childGuard
    simpa only [d1848, d1278, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4813 (pattern : Twelve) (guard : d1848 pattern = 1) : d872 pattern ≤ (0 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4265 pattern childGuard
    simpa only [d1848, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4811 pattern childGuard
    simpa only [d1848, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4814 (pattern : Twelve) (guard : d1848 pattern = 1) : d1284 pattern ≤ (0 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1284, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4812 pattern childGuard
    simpa only [d1284, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1284, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4813 pattern childGuard
    simpa only [d1284, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4815 (pattern : Twelve) (guard : d1848 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1293, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1670 pattern childGuard
    simpa only [d1293, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1293, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4814 pattern childGuard
    simpa only [d1293, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4816 (pattern : Twelve) (guard : d1848 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1294 pattern := by
  omega
theorem c4817 (pattern : Twelve) (guard : d1848 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4815 pattern childGuard
    simpa only [d1305, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4816 pattern childGuard
    simpa only [d1305, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4818 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1346 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4819 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1436, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4817 pattern childGuard
    simpa only [d1869, d1436, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1436, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4818 pattern childGuard
    simpa only [d1869, d1436, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4820 (pattern : Twelve) (guard : d1848 pattern = 1) : d1278 pattern ≤ (0 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1278, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1469 pattern childGuard
    simpa only [d1848, d1278, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1278, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4778 pattern childGuard
    simpa only [d1848, d1278, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4821 (pattern : Twelve) (guard : d0 pattern = 1) : d872 pattern ≤ (0 : Int) + d1277 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4822 (pattern : Twelve) (guard : d1848 pattern = 1) : d872 pattern ≤ (0 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4265 pattern childGuard
    simpa only [d1848, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4821 pattern childGuard
    simpa only [d1848, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4823 (pattern : Twelve) (guard : d1848 pattern = 1) : d1284 pattern ≤ (0 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1284, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4820 pattern childGuard
    simpa only [d1284, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1284, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4822 pattern childGuard
    simpa only [d1284, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4824 (pattern : Twelve) (guard : d1848 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1293, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4485 pattern childGuard
    simpa only [d1293, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1293, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4823 pattern childGuard
    simpa only [d1293, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4825 (pattern : Twelve) (guard : d0 pattern = 1) : d19 pattern ≤ (0 : Int) + d20 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4826 (pattern : Twelve) (guard : d1848 pattern = 1) : d19 pattern ≤ (0 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4825 pattern childGuard
    simpa only [d1848, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4827 (pattern : Twelve) (guard : d1848 pattern = 1) : d19 pattern ≤ (0 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4538 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4826 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4828 (pattern : Twelve) (guard : d1848 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1294, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4827 pattern childGuard
    simpa only [d1294, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1294, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1294, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4829 (pattern : Twelve) (guard : d1848 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4824 pattern childGuard
    simpa only [d1305, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4828 pattern childGuard
    simpa only [d1305, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4830 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1348 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4831 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1436, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4829 pattern childGuard
    simpa only [d1869, d1436, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1436, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4830 pattern childGuard
    simpa only [d1869, d1436, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4832 (pattern : Twelve) (guard : d1848 pattern = 1) : d1284 pattern ≤ (0 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1284, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4820 pattern childGuard
    simpa only [d1284, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1284, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4266 pattern childGuard
    simpa only [d1284, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4833 (pattern : Twelve) (guard : d1848 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1293, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4700 pattern childGuard
    simpa only [d1293, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1293, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4832 pattern childGuard
    simpa only [d1293, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4834 (pattern : Twelve) (guard : d1848 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4833 pattern childGuard
    simpa only [d1305, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4789 pattern childGuard
    simpa only [d1305, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4835 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1436, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4834 pattern childGuard
    simpa only [d1869, d1436, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1436, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1436, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4836 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4831 pattern childGuard
    simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4835 pattern childGuard
    simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4837 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4819 pattern childGuard
    simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4836 pattern childGuard
    simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4838 (pattern : Twelve) (guard : d1848 pattern = 1) : d1309 pattern ≤ (0 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1309, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4815 pattern childGuard
    simpa only [d1309, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1309, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4795 pattern childGuard
    simpa only [d1309, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4839 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1437, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4838 pattern childGuard
    simpa only [d1869, d1437, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1437, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4818 pattern childGuard
    simpa only [d1869, d1437, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4840 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (0 : Int) + d20 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4841 (pattern : Twelve) (guard : d1848 pattern = 1) : d1283 pattern ≤ (0 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1283, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d1283, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1283, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4840 pattern childGuard
    simpa only [d1848, d1283, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4842 (pattern : Twelve) (guard : d1848 pattern = 1) : d1283 pattern ≤ (0 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4552 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4841 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4843 (pattern : Twelve) (guard : d1848 pattern = 1) : d1301 pattern ≤ (0 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1301, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4842 pattern childGuard
    simpa only [d1301, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1301, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1301, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4844 (pattern : Twelve) (guard : d1848 pattern = 1) : d1309 pattern ≤ (0 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1309, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4824 pattern childGuard
    simpa only [d1309, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1309, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4843 pattern childGuard
    simpa only [d1309, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4845 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1437, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4844 pattern childGuard
    simpa only [d1869, d1437, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1437, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4830 pattern childGuard
    simpa only [d1869, d1437, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4846 (pattern : Twelve) (guard : d1848 pattern = 1) : d1309 pattern ≤ (0 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1309, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4833 pattern childGuard
    simpa only [d1309, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1309, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4802 pattern childGuard
    simpa only [d1309, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4847 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1437, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4846 pattern childGuard
    simpa only [d1869, d1437, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1437, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1437, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4848 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4845 pattern childGuard
    simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4847 pattern childGuard
    simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4849 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4839 pattern childGuard
    simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4848 pattern childGuard
    simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4850 (pattern : Twelve) (guard : d1869 pattern = 1) : d1441 pattern ≤ (0 : Int) + d1353 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4837 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4849 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4851 (pattern : Twelve) (guard : d1869 pattern = 1) : d1443 pattern ≤ (0 : Int) + d1354 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1443, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4810 pattern childGuard
    simpa only [d1443, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1443, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4850 pattern childGuard
    simpa only [d1443, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4852 (pattern : Twelve) (guard : d1848 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1656 pattern := by
  omega
theorem c4853 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1715, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4852 pattern childGuard
    simpa only [d1869, d1715, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1715, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4380 pattern childGuard
    simpa only [d1869, d1715, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4854 (pattern : Twelve) (guard : d1848 pattern = 1) : d1649 pattern ≤ (0 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1649, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4538 pattern childGuard
    simpa only [d1649, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1649, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4573 pattern childGuard
    simpa only [d1649, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4855 (pattern : Twelve) (guard : d1848 pattern = 1) : d1650 pattern ≤ (0 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1650, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4577 pattern childGuard
    simpa only [d1650, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1650, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1650, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4856 (pattern : Twelve) (guard : d1848 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1656, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4854 pattern childGuard
    simpa only [d1656, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1656, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4855 pattern childGuard
    simpa only [d1656, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4857 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1659 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4858 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1715, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4856 pattern childGuard
    simpa only [d1869, d1715, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1715, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4857 pattern childGuard
    simpa only [d1869, d1715, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4859 (pattern : Twelve) (guard : d1848 pattern = 1) : d1324 pattern ≤ (0 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4573 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1523 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4860 (pattern : Twelve) (guard : d1848 pattern = 1) : d1649 pattern ≤ (0 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1649, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4788 pattern childGuard
    simpa only [d1649, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1649, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4859 pattern childGuard
    simpa only [d1649, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4861 (pattern : Twelve) (guard : d1848 pattern = 1) : d25 pattern ≤ (0 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4577 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1526 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4862 (pattern : Twelve) (guard : d1848 pattern = 1) : d1650 pattern ≤ (0 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1650, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4861 pattern childGuard
    simpa only [d1650, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1650, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1650, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4863 (pattern : Twelve) (guard : d1848 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1656, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4860 pattern childGuard
    simpa only [d1656, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1656, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4862 pattern childGuard
    simpa only [d1656, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4864 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1715, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4863 pattern childGuard
    simpa only [d1869, d1715, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1715, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1715, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4865 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4858 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4864 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4866 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4853 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4865 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4867 (pattern : Twelve) (guard : d1848 pattern = 1) : d1649 pattern ≤ (0 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1649, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1741 pattern childGuard
    simpa only [d1649, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1649, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4573 pattern childGuard
    simpa only [d1649, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4868 (pattern : Twelve) (guard : d1848 pattern = 1) : d1650 pattern ≤ (0 : Int) + d1650 pattern := by
  omega
theorem c4869 (pattern : Twelve) (guard : d1848 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1656, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4867 pattern childGuard
    simpa only [d1656, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1656, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4868 pattern childGuard
    simpa only [d1656, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4870 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1715, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4869 pattern childGuard
    simpa only [d1869, d1715, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1715, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4380 pattern childGuard
    simpa only [d1869, d1715, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4871 (pattern : Twelve) (guard : d0 pattern = 1) : d1324 pattern ≤ (0 : Int) + d22 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4872 (pattern : Twelve) (guard : d1848 pattern = 1) : d1324 pattern ≤ (0 : Int) + d1665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c388 pattern childGuard
    simpa only [d1848, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4871 pattern childGuard
    simpa only [d1848, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4873 (pattern : Twelve) (guard : d1848 pattern = 1) : d1324 pattern ≤ (0 : Int) + d1666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4573 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4872 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4874 (pattern : Twelve) (guard : d1848 pattern = 1) : d1649 pattern ≤ (0 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1649, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4538 pattern childGuard
    simpa only [d1649, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1649, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4873 pattern childGuard
    simpa only [d1649, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4875 (pattern : Twelve) (guard : d1848 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1656, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4874 pattern childGuard
    simpa only [d1656, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1656, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4862 pattern childGuard
    simpa only [d1656, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4876 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1673 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4877 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1715, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4875 pattern childGuard
    simpa only [d1869, d1715, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1715, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4876 pattern childGuard
    simpa only [d1869, d1715, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4878 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1676 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4877 pattern childGuard
    simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4864 pattern childGuard
    simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4879 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1677 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4870 pattern childGuard
    simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4878 pattern childGuard
    simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4880 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1678 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4866 pattern childGuard
    simpa only [d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4879 pattern childGuard
    simpa only [d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4881 (pattern : Twelve) (guard : d0 pattern = 1) : d359 pattern ≤ (0 : Int) + d111 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4882 (pattern : Twelve) (guard : d1868 pattern = 1) : d361 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d361, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4323 pattern childGuard
    simpa only [d1868, d361, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d361, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4881 pattern childGuard
    simpa only [d1868, d361, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4883 (pattern : Twelve) (guard : d0 pattern = 1) : d356 pattern ≤ (0 : Int) + d113 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4884 (pattern : Twelve) (guard : d1868 pattern = 1) : d356 pattern ≤ (0 : Int) + d115 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4330 pattern childGuard
    simpa only [d1868, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4883 pattern childGuard
    simpa only [d1868, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4885 (pattern : Twelve) (guard : d1868 pattern = 1) : d362 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d362, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4882 pattern childGuard
    simpa only [d362, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d362, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4884 pattern childGuard
    simpa only [d362, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4886 (pattern : Twelve) (guard : d0 pattern = 1) : d360 pattern ≤ (0 : Int) + d111 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4887 (pattern : Twelve) (guard : d1868 pattern = 1) : d360 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4338 pattern childGuard
    simpa only [d1868, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4886 pattern childGuard
    simpa only [d1868, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4888 (pattern : Twelve) (guard : d1868 pattern = 1) : d363 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d363, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4887 pattern childGuard
    simpa only [d363, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d363, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4884 pattern childGuard
    simpa only [d363, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4889 (pattern : Twelve) (guard : d1868 pattern = 1) : d364 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4885 pattern childGuard
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4888 pattern childGuard
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4890 (pattern : Twelve) (guard : d1868 pattern = 1) : d365 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4889 pattern childGuard
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4888 pattern childGuard
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4891 (pattern : Twelve) (guard : d0 pattern = 1) : d1024 pattern ≤ (0 : Int) + d867 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4892 (pattern : Twelve) (guard : d1868 pattern = 1) : d1025 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1025, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4348 pattern childGuard
    simpa only [d1868, d1025, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1025, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4891 pattern childGuard
    simpa only [d1868, d1025, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4893 (pattern : Twelve) (guard : d0 pattern = 1) : d1022 pattern ≤ (0 : Int) + d868 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4894 (pattern : Twelve) (guard : d1868 pattern = 1) : d1022 pattern ≤ (0 : Int) + d870 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4352 pattern childGuard
    simpa only [d1868, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4893 pattern childGuard
    simpa only [d1868, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4895 (pattern : Twelve) (guard : d1868 pattern = 1) : d1026 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1026, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4892 pattern childGuard
    simpa only [d1026, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1026, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4894 pattern childGuard
    simpa only [d1026, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4896 (pattern : Twelve) (guard : d0 pattern = 1) : d1021 pattern ≤ (0 : Int) + d867 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4897 (pattern : Twelve) (guard : d1868 pattern = 1) : d1021 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4357 pattern childGuard
    simpa only [d1868, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4896 pattern childGuard
    simpa only [d1868, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4898 (pattern : Twelve) (guard : d1868 pattern = 1) : d1027 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1027, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4897 pattern childGuard
    simpa only [d1027, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1027, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4894 pattern childGuard
    simpa only [d1027, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4899 (pattern : Twelve) (guard : d1868 pattern = 1) : d1028 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4895 pattern childGuard
    simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4898 pattern childGuard
    simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
