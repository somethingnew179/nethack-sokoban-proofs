/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons004
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c700 (pattern : Twelve) (guard : d0 pattern = 1) : d223 pattern ≤ (0 : Int) + d217 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c701 (pattern : Twelve) (guard : d1842 pattern = 1) : d228 pattern ≤ (0 : Int) + d345 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d228, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c641 pattern childGuard
    simpa only [d1842, d228, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d228, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c700 pattern childGuard
    simpa only [d1842, d228, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c702 (pattern : Twelve) (guard : d0 pattern = 1) : d225 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c703 (pattern : Twelve) (guard : d1842 pattern = 1) : d229 pattern ≤ (0 : Int) + d346 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d229, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c646 pattern childGuard
    simpa only [d1842, d229, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d229, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c702 pattern childGuard
    simpa only [d1842, d229, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c704 (pattern : Twelve) (guard : d1842 pattern = 1) : d231 pattern ≤ (0 : Int) + d348 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d231, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c701 pattern childGuard
    simpa only [d231, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d231, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c703 pattern childGuard
    simpa only [d231, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c705 (pattern : Twelve) (guard : d0 pattern = 1) : d227 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c706 (pattern : Twelve) (guard : d1842 pattern = 1) : d230 pattern ≤ (0 : Int) + d347 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d230, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c652 pattern childGuard
    simpa only [d1842, d230, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d230, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c705 pattern childGuard
    simpa only [d1842, d230, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c707 (pattern : Twelve) (guard : d1842 pattern = 1) : d232 pattern ≤ (0 : Int) + d349 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d232, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c706 pattern childGuard
    simpa only [d232, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d232, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c703 pattern childGuard
    simpa only [d232, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c708 (pattern : Twelve) (guard : d1842 pattern = 1) : d233 pattern ≤ (0 : Int) + d350 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d233, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c704 pattern childGuard
    simpa only [d233, d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d233, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c707 pattern childGuard
    simpa only [d233, d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c709 (pattern : Twelve) (guard : d1842 pattern = 1) : d234 pattern ≤ (0 : Int) + d351 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d234, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c708 pattern childGuard
    simpa only [d234, d351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d234, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c707 pattern childGuard
    simpa only [d234, d351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c710 (pattern : Twelve) (guard : d0 pattern = 1) : d928 pattern ≤ (0 : Int) + d922 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c711 (pattern : Twelve) (guard : d1842 pattern = 1) : d933 pattern ≤ (0 : Int) + d1011 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d933, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c660 pattern childGuard
    simpa only [d1842, d933, d1011, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d933, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c710 pattern childGuard
    simpa only [d1842, d933, d1011, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c712 (pattern : Twelve) (guard : d0 pattern = 1) : d930 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c713 (pattern : Twelve) (guard : d1842 pattern = 1) : d934 pattern ≤ (0 : Int) + d1012 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d934, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c665 pattern childGuard
    simpa only [d1842, d934, d1012, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d934, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c712 pattern childGuard
    simpa only [d1842, d934, d1012, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c714 (pattern : Twelve) (guard : d1842 pattern = 1) : d936 pattern ≤ (0 : Int) + d1014 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d936, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c711 pattern childGuard
    simpa only [d936, d1014, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d936, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c713 pattern childGuard
    simpa only [d936, d1014, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c715 (pattern : Twelve) (guard : d0 pattern = 1) : d932 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c716 (pattern : Twelve) (guard : d1842 pattern = 1) : d935 pattern ≤ (0 : Int) + d1013 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d935, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c671 pattern childGuard
    simpa only [d1842, d935, d1013, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d935, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c715 pattern childGuard
    simpa only [d1842, d935, d1013, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c717 (pattern : Twelve) (guard : d1842 pattern = 1) : d937 pattern ≤ (0 : Int) + d1015 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d937, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c716 pattern childGuard
    simpa only [d937, d1015, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d937, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c713 pattern childGuard
    simpa only [d937, d1015, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c718 (pattern : Twelve) (guard : d1842 pattern = 1) : d938 pattern ≤ (0 : Int) + d1016 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d938, d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c714 pattern childGuard
    simpa only [d938, d1016, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d938, d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c717 pattern childGuard
    simpa only [d938, d1016, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c719 (pattern : Twelve) (guard : d1842 pattern = 1) : d939 pattern ≤ (0 : Int) + d1017 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d939, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c718 pattern childGuard
    simpa only [d939, d1017, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d939, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c717 pattern childGuard
    simpa only [d939, d1017, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c720 (pattern : Twelve) (guard : d0 pattern = 1) : d1369 pattern ≤ (0 : Int) + d1363 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c721 (pattern : Twelve) (guard : d1842 pattern = 1) : d1373 pattern ≤ (0 : Int) + d1428 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d1373, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c679 pattern childGuard
    simpa only [d1842, d1373, d1428, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d1373, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c720 pattern childGuard
    simpa only [d1842, d1373, d1428, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c722 (pattern : Twelve) (guard : d0 pattern = 1) : d1371 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c723 (pattern : Twelve) (guard : d1842 pattern = 1) : d1374 pattern ≤ (0 : Int) + d1429 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d1374, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c684 pattern childGuard
    simpa only [d1842, d1374, d1429, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d1374, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c722 pattern childGuard
    simpa only [d1842, d1374, d1429, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c724 (pattern : Twelve) (guard : d1842 pattern = 1) : d1376 pattern ≤ (0 : Int) + d1431 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1376, d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c721 pattern childGuard
    simpa only [d1376, d1431, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1376, d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c723 pattern childGuard
    simpa only [d1376, d1431, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c725 (pattern : Twelve) (guard : d0 pattern = 1) : d1369 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c726 (pattern : Twelve) (guard : d1842 pattern = 1) : d1375 pattern ≤ (0 : Int) + d1430 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d1375, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c690 pattern childGuard
    simpa only [d1842, d1375, d1430, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d1375, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c725 pattern childGuard
    simpa only [d1842, d1375, d1430, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c727 (pattern : Twelve) (guard : d1842 pattern = 1) : d1377 pattern ≤ (0 : Int) + d1432 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1377, d1432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c726 pattern childGuard
    simpa only [d1377, d1432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1377, d1432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c723 pattern childGuard
    simpa only [d1377, d1432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c728 (pattern : Twelve) (guard : d1842 pattern = 1) : d1378 pattern ≤ (0 : Int) + d1433 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1378, d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c724 pattern childGuard
    simpa only [d1378, d1433, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1378, d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c727 pattern childGuard
    simpa only [d1378, d1433, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c729 (pattern : Twelve) (guard : d1842 pattern = 1) : d1379 pattern ≤ (0 : Int) + d1434 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1379, d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c728 pattern childGuard
    simpa only [d1379, d1434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1379, d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c727 pattern childGuard
    simpa only [d1379, d1434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c730 (pattern : Twelve) (guard : d0 pattern = 1) : d1687 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c731 (pattern : Twelve) (guard : d1842 pattern = 1) : d1688 pattern ≤ (0 : Int) + d1714 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d1688, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c696 pattern childGuard
    simpa only [d1842, d1688, d1714, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d1688, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c730 pattern childGuard
    simpa only [d1842, d1688, d1714, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c732 (pattern : Twelve) (guard : d1 pattern = 1) : d91 pattern ≤ (0 : Int) + d91 pattern := by
  omega
theorem c733 (pattern : Twelve) (guard : d0 pattern = 1) : d92 pattern ≤ (0 : Int) + d208 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c734 (pattern : Twelve) (guard : d1844 pattern = 1) : d102 pattern ≤ (0 : Int) + d352 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d102, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c732 pattern childGuard
    simpa only [d1844, d102, d352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d102, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c733 pattern childGuard
    simpa only [d1844, d102, d352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c735 (pattern : Twelve) (guard : d0 pattern = 1) : d213 pattern ≤ (0 : Int) + d353 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c736 (pattern : Twelve) (guard : d1845 pattern = 1) : d222 pattern ≤ (0 : Int) + d358 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d222, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c734 pattern childGuard
    simpa only [d1845, d222, d358, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d222, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c735 pattern childGuard
    simpa only [d1845, d222, d358, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c737 (pattern : Twelve) (guard : d0 pattern = 1) : d223 pattern ≤ (0 : Int) + d359 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c738 (pattern : Twelve) (guard : d1846 pattern = 1) : d228 pattern ≤ (0 : Int) + d361 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d228, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c736 pattern childGuard
    simpa only [d1846, d228, d361, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d228, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c737 pattern childGuard
    simpa only [d1846, d228, d361, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c739 (pattern : Twelve) (guard : d1 pattern = 1) : d97 pattern ≤ (0 : Int) + d97 pattern := by
  omega
theorem c740 (pattern : Twelve) (guard : d0 pattern = 1) : d98 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c741 (pattern : Twelve) (guard : d1844 pattern = 1) : d106 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d106, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c739 pattern childGuard
    simpa only [d1844, d106, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d106, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c740 pattern childGuard
    simpa only [d1844, d106, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c742 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d356 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c743 (pattern : Twelve) (guard : d1845 pattern = 1) : d224 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c741 pattern childGuard
    simpa only [d1845, d224, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c742 pattern childGuard
    simpa only [d1845, d224, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c744 (pattern : Twelve) (guard : d0 pattern = 1) : d225 pattern ≤ (0 : Int) + d356 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c745 (pattern : Twelve) (guard : d1846 pattern = 1) : d229 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c743 pattern childGuard
    simpa only [d1846, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c744 pattern childGuard
    simpa only [d1846, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c746 (pattern : Twelve) (guard : d1846 pattern = 1) : d231 pattern ≤ (0 : Int) + d362 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d231, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c738 pattern childGuard
    simpa only [d231, d362, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d231, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c745 pattern childGuard
    simpa only [d231, d362, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c747 (pattern : Twelve) (guard : d0 pattern = 1) : d92 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c748 (pattern : Twelve) (guard : d1844 pattern = 1) : d102 pattern ≤ (0 : Int) + d357 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d102, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c732 pattern childGuard
    simpa only [d1844, d102, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d102, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c747 pattern childGuard
    simpa only [d1844, d102, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c749 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d355 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c750 (pattern : Twelve) (guard : d1845 pattern = 1) : d226 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d226, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c748 pattern childGuard
    simpa only [d1845, d226, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d226, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c749 pattern childGuard
    simpa only [d1845, d226, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c751 (pattern : Twelve) (guard : d0 pattern = 1) : d227 pattern ≤ (0 : Int) + d360 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c752 (pattern : Twelve) (guard : d1846 pattern = 1) : d230 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c750 pattern childGuard
    simpa only [d1846, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c751 pattern childGuard
    simpa only [d1846, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c753 (pattern : Twelve) (guard : d1846 pattern = 1) : d232 pattern ≤ (0 : Int) + d363 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d232, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c752 pattern childGuard
    simpa only [d232, d363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d232, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c745 pattern childGuard
    simpa only [d232, d363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c754 (pattern : Twelve) (guard : d1846 pattern = 1) : d233 pattern ≤ (0 : Int) + d364 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d233, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c746 pattern childGuard
    simpa only [d233, d364, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d233, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c753 pattern childGuard
    simpa only [d233, d364, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c755 (pattern : Twelve) (guard : d1846 pattern = 1) : d234 pattern ≤ (0 : Int) + d365 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d234, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c754 pattern childGuard
    simpa only [d234, d365, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d234, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c753 pattern childGuard
    simpa only [d234, d365, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c756 (pattern : Twelve) (guard : d1 pattern = 1) : d853 pattern ≤ (0 : Int) + d853 pattern := by
  omega
theorem c757 (pattern : Twelve) (guard : d0 pattern = 1) : d854 pattern ≤ (0 : Int) + d913 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c758 (pattern : Twelve) (guard : d1844 pattern = 1) : d861 pattern ≤ (0 : Int) + d1018 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d861, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c756 pattern childGuard
    simpa only [d1844, d861, d1018, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d861, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c757 pattern childGuard
    simpa only [d1844, d861, d1018, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c759 (pattern : Twelve) (guard : d0 pattern = 1) : d918 pattern ≤ (0 : Int) + d1019 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c760 (pattern : Twelve) (guard : d1845 pattern = 1) : d927 pattern ≤ (0 : Int) + d1023 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d927, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c758 pattern childGuard
    simpa only [d1845, d927, d1023, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d927, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c759 pattern childGuard
    simpa only [d1845, d927, d1023, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c761 (pattern : Twelve) (guard : d0 pattern = 1) : d928 pattern ≤ (0 : Int) + d1024 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c762 (pattern : Twelve) (guard : d1846 pattern = 1) : d933 pattern ≤ (0 : Int) + d1025 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d933, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c760 pattern childGuard
    simpa only [d1846, d933, d1025, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d933, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c761 pattern childGuard
    simpa only [d1846, d933, d1025, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c763 (pattern : Twelve) (guard : d1 pattern = 1) : d857 pattern ≤ (0 : Int) + d857 pattern := by
  omega
theorem c764 (pattern : Twelve) (guard : d0 pattern = 1) : d858 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c765 (pattern : Twelve) (guard : d1844 pattern = 1) : d864 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d864, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c763 pattern childGuard
    simpa only [d1844, d864, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d864, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c764 pattern childGuard
    simpa only [d1844, d864, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c766 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1022 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c767 (pattern : Twelve) (guard : d1845 pattern = 1) : d929 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c765 pattern childGuard
    simpa only [d1845, d929, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c766 pattern childGuard
    simpa only [d1845, d929, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c768 (pattern : Twelve) (guard : d0 pattern = 1) : d930 pattern ≤ (0 : Int) + d1022 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c769 (pattern : Twelve) (guard : d1846 pattern = 1) : d934 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c767 pattern childGuard
    simpa only [d1846, d934, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c768 pattern childGuard
    simpa only [d1846, d934, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c770 (pattern : Twelve) (guard : d1846 pattern = 1) : d936 pattern ≤ (0 : Int) + d1026 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d936, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c762 pattern childGuard
    simpa only [d936, d1026, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d936, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c769 pattern childGuard
    simpa only [d936, d1026, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c771 (pattern : Twelve) (guard : d0 pattern = 1) : d854 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c772 (pattern : Twelve) (guard : d1844 pattern = 1) : d861 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d861, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c756 pattern childGuard
    simpa only [d1844, d861, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d861, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c771 pattern childGuard
    simpa only [d1844, d861, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c773 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1021 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c774 (pattern : Twelve) (guard : d1845 pattern = 1) : d931 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c772 pattern childGuard
    simpa only [d1845, d931, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c773 pattern childGuard
    simpa only [d1845, d931, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c775 (pattern : Twelve) (guard : d0 pattern = 1) : d932 pattern ≤ (0 : Int) + d1021 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c776 (pattern : Twelve) (guard : d1846 pattern = 1) : d935 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c774 pattern childGuard
    simpa only [d1846, d935, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c775 pattern childGuard
    simpa only [d1846, d935, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c777 (pattern : Twelve) (guard : d1846 pattern = 1) : d937 pattern ≤ (0 : Int) + d1027 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d937, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c776 pattern childGuard
    simpa only [d937, d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d937, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c769 pattern childGuard
    simpa only [d937, d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c778 (pattern : Twelve) (guard : d1846 pattern = 1) : d938 pattern ≤ (0 : Int) + d1028 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d938, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c770 pattern childGuard
    simpa only [d938, d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d938, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c777 pattern childGuard
    simpa only [d938, d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c779 (pattern : Twelve) (guard : d1846 pattern = 1) : d939 pattern ≤ (0 : Int) + d1029 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d939, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c778 pattern childGuard
    simpa only [d939, d1029, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d939, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c777 pattern childGuard
    simpa only [d939, d1029, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c780 (pattern : Twelve) (guard : d1 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1305 pattern := by
  omega
theorem c781 (pattern : Twelve) (guard : d0 pattern = 1) : d1306 pattern ≤ (0 : Int) + d1357 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c782 (pattern : Twelve) (guard : d1844 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1435 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1313, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c780 pattern childGuard
    simpa only [d1844, d1313, d1435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1313, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c781 pattern childGuard
    simpa only [d1844, d1313, d1435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c783 (pattern : Twelve) (guard : d0 pattern = 1) : d1360 pattern ≤ (0 : Int) + d1436 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c784 (pattern : Twelve) (guard : d1845 pattern = 1) : d1368 pattern ≤ (0 : Int) + d1438 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d1368, d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c782 pattern childGuard
    simpa only [d1845, d1368, d1438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d1368, d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c783 pattern childGuard
    simpa only [d1845, d1368, d1438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c785 (pattern : Twelve) (guard : d0 pattern = 1) : d1369 pattern ≤ (0 : Int) + d1436 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c786 (pattern : Twelve) (guard : d1846 pattern = 1) : d1373 pattern ≤ (0 : Int) + d1439 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d1373, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c784 pattern childGuard
    simpa only [d1846, d1373, d1439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d1373, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c785 pattern childGuard
    simpa only [d1846, d1373, d1439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c787 (pattern : Twelve) (guard : d1 pattern = 1) : d1309 pattern ≤ (0 : Int) + d1309 pattern := by
  omega
theorem c788 (pattern : Twelve) (guard : d0 pattern = 1) : d1310 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c789 (pattern : Twelve) (guard : d1844 pattern = 1) : d1316 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1316, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c787 pattern childGuard
    simpa only [d1844, d1316, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1316, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c788 pattern childGuard
    simpa only [d1844, d1316, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c790 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1437 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c791 (pattern : Twelve) (guard : d1845 pattern = 1) : d1370 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d1370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c789 pattern childGuard
    simpa only [d1845, d1370, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d1370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c790 pattern childGuard
    simpa only [d1845, d1370, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c792 (pattern : Twelve) (guard : d0 pattern = 1) : d1371 pattern ≤ (0 : Int) + d1437 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c793 (pattern : Twelve) (guard : d1846 pattern = 1) : d1374 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c791 pattern childGuard
    simpa only [d1846, d1374, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c792 pattern childGuard
    simpa only [d1846, d1374, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c794 (pattern : Twelve) (guard : d1846 pattern = 1) : d1376 pattern ≤ (0 : Int) + d1440 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1376, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c786 pattern childGuard
    simpa only [d1376, d1440, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1376, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c793 pattern childGuard
    simpa only [d1376, d1440, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c795 (pattern : Twelve) (guard : d0 pattern = 1) : d1306 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c796 (pattern : Twelve) (guard : d1844 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1313, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c780 pattern childGuard
    simpa only [d1844, d1313, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1313, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c795 pattern childGuard
    simpa only [d1844, d1313, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c797 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1436 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c798 (pattern : Twelve) (guard : d1845 pattern = 1) : d1372 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d1372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c796 pattern childGuard
    simpa only [d1845, d1372, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d1372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c797 pattern childGuard
    simpa only [d1845, d1372, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c799 (pattern : Twelve) (guard : d1846 pattern = 1) : d1375 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d1375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c798 pattern childGuard
    simpa only [d1846, d1375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d1375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c785 pattern childGuard
    simpa only [d1846, d1375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c800 (pattern : Twelve) (guard : d1846 pattern = 1) : d1377 pattern ≤ (0 : Int) + d1441 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1377, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c799 pattern childGuard
    simpa only [d1377, d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1377, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c793 pattern childGuard
    simpa only [d1377, d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c801 (pattern : Twelve) (guard : d1846 pattern = 1) : d1378 pattern ≤ (0 : Int) + d1442 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1378, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c794 pattern childGuard
    simpa only [d1378, d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1378, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c800 pattern childGuard
    simpa only [d1378, d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c802 (pattern : Twelve) (guard : d1846 pattern = 1) : d1379 pattern ≤ (0 : Int) + d1443 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1379, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c801 pattern childGuard
    simpa only [d1379, d1443, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1379, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c800 pattern childGuard
    simpa only [d1379, d1443, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c803 (pattern : Twelve) (guard : d1 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1656 pattern := by
  omega
theorem c804 (pattern : Twelve) (guard : d0 pattern = 1) : d1657 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c805 (pattern : Twelve) (guard : d1844 pattern = 1) : d1660 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1660, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c803 pattern childGuard
    simpa only [d1844, d1660, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1660, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c804 pattern childGuard
    simpa only [d1844, d1660, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c806 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1715 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c807 (pattern : Twelve) (guard : d1845 pattern = 1) : d1686 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c805 pattern childGuard
    simpa only [d1845, d1686, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c806 pattern childGuard
    simpa only [d1845, d1686, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c808 (pattern : Twelve) (guard : d0 pattern = 1) : d1687 pattern ≤ (0 : Int) + d1715 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c809 (pattern : Twelve) (guard : d1846 pattern = 1) : d1688 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c807 pattern childGuard
    simpa only [d1846, d1688, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c808 pattern childGuard
    simpa only [d1846, d1688, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c810 (pattern : Twelve) (guard : d0 pattern = 1) : d171 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c811 (pattern : Twelve) (guard : d1837 pattern = 1) : d235 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1837, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c810 pattern childGuard
    simpa only [d1837, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c812 (pattern : Twelve) (guard : d0 pattern = 1) : d172 pattern ≤ (0 : Int) + d27 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c813 (pattern : Twelve) (guard : d1837 pattern = 1) : d236 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d236, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d1837, d236, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d236, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c812 pattern childGuard
    simpa only [d1837, d236, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c814 (pattern : Twelve) (guard : d1837 pattern = 1) : d256 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d256, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c811 pattern childGuard
    simpa only [d256, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d256, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c813 pattern childGuard
    simpa only [d256, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c815 (pattern : Twelve) (guard : d0 pattern = 1) : d172 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c816 (pattern : Twelve) (guard : d1837 pattern = 1) : d237 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1837, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c815 pattern childGuard
    simpa only [d1837, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c817 (pattern : Twelve) (guard : d0 pattern = 1) : d173 pattern ≤ (0 : Int) + d29 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c818 (pattern : Twelve) (guard : d1837 pattern = 1) : d238 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d238, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c87 pattern childGuard
    simpa only [d1837, d238, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d238, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c817 pattern childGuard
    simpa only [d1837, d238, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c819 (pattern : Twelve) (guard : d1837 pattern = 1) : d257 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d257, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c816 pattern childGuard
    simpa only [d257, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d257, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c818 pattern childGuard
    simpa only [d257, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c820 (pattern : Twelve) (guard : d1837 pattern = 1) : d272 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d272, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c814 pattern childGuard
    simpa only [d272, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d272, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c819 pattern childGuard
    simpa only [d272, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c821 (pattern : Twelve) (guard : d0 pattern = 1) : d175 pattern ≤ (0 : Int) + d31 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c822 (pattern : Twelve) (guard : d1837 pattern = 1) : d239 pattern ≤ (0 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d239, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d239, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d239, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c821 pattern childGuard
    simpa only [d1837, d239, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c823 (pattern : Twelve) (guard : d0 pattern = 1) : d176 pattern ≤ (0 : Int) + d32 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c824 (pattern : Twelve) (guard : d1837 pattern = 1) : d240 pattern ≤ (0 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d240, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d240, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d240, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c823 pattern childGuard
    simpa only [d1837, d240, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c825 (pattern : Twelve) (guard : d1837 pattern = 1) : d258 pattern ≤ (0 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d258, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c822 pattern childGuard
    simpa only [d258, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d258, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c824 pattern childGuard
    simpa only [d258, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c826 (pattern : Twelve) (guard : d0 pattern = 1) : d176 pattern ≤ (0 : Int) + d33 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c827 (pattern : Twelve) (guard : d1837 pattern = 1) : d240 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d240, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d240, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d240, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c826 pattern childGuard
    simpa only [d1837, d240, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c828 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d29 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c829 (pattern : Twelve) (guard : d1837 pattern = 1) : d241 pattern ≤ (0 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d241, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d241, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d241, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c828 pattern childGuard
    simpa only [d1837, d241, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c830 (pattern : Twelve) (guard : d1837 pattern = 1) : d259 pattern ≤ (0 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d259, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c827 pattern childGuard
    simpa only [d259, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d259, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c829 pattern childGuard
    simpa only [d259, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c831 (pattern : Twelve) (guard : d1837 pattern = 1) : d273 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d273, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c825 pattern childGuard
    simpa only [d273, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d273, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c830 pattern childGuard
    simpa only [d273, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c832 (pattern : Twelve) (guard : d1837 pattern = 1) : d284 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d284, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c820 pattern childGuard
    simpa only [d284, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d284, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c831 pattern childGuard
    simpa only [d284, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c833 (pattern : Twelve) (guard : d0 pattern = 1) : d175 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c834 (pattern : Twelve) (guard : d1837 pattern = 1) : d242 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1837, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c833 pattern childGuard
    simpa only [d1837, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c835 (pattern : Twelve) (guard : d0 pattern = 1) : d176 pattern ≤ (0 : Int) + d27 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c836 (pattern : Twelve) (guard : d1837 pattern = 1) : d243 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d243, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d1837, d243, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d243, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c835 pattern childGuard
    simpa only [d1837, d243, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c837 (pattern : Twelve) (guard : d1837 pattern = 1) : d260 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d260, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c834 pattern childGuard
    simpa only [d260, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d260, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c836 pattern childGuard
    simpa only [d260, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c838 (pattern : Twelve) (guard : d0 pattern = 1) : d176 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c839 (pattern : Twelve) (guard : d1837 pattern = 1) : d244 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1837, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c838 pattern childGuard
    simpa only [d1837, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
