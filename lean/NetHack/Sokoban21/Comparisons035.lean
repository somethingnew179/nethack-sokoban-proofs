/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons034
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c4900 (pattern : Twelve) (guard : d1868 pattern = 1) : d1029 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4899 pattern childGuard
    simpa only [d1029, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4898 pattern childGuard
    simpa only [d1029, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4901 (pattern : Twelve) (guard : d0 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1319 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4902 (pattern : Twelve) (guard : d1868 pattern = 1) : d1439 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1439, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4367 pattern childGuard
    simpa only [d1868, d1439, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1439, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4901 pattern childGuard
    simpa only [d1868, d1439, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4903 (pattern : Twelve) (guard : d0 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1320 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4904 (pattern : Twelve) (guard : d1868 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1322 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4371 pattern childGuard
    simpa only [d1868, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4903 pattern childGuard
    simpa only [d1868, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4905 (pattern : Twelve) (guard : d1868 pattern = 1) : d1440 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1440, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4902 pattern childGuard
    simpa only [d1440, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1440, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4904 pattern childGuard
    simpa only [d1440, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4906 (pattern : Twelve) (guard : d1868 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4366 pattern childGuard
    simpa only [d1868, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4901 pattern childGuard
    simpa only [d1868, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4907 (pattern : Twelve) (guard : d1868 pattern = 1) : d1441 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1441, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4906 pattern childGuard
    simpa only [d1441, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1441, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4904 pattern childGuard
    simpa only [d1441, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4908 (pattern : Twelve) (guard : d1868 pattern = 1) : d1442 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4905 pattern childGuard
    simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4907 pattern childGuard
    simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4909 (pattern : Twelve) (guard : d1868 pattern = 1) : d1443 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4908 pattern childGuard
    simpa only [d1443, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4907 pattern childGuard
    simpa only [d1443, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4910 (pattern : Twelve) (guard : d0 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1663 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4911 (pattern : Twelve) (guard : d1868 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4381 pattern childGuard
    simpa only [d1868, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4910 pattern childGuard
    simpa only [d1868, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4912 (pattern : Twelve) (guard : d0 pattern = 1) : d353 pattern ≤ (0 : Int) + d213 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4913 (pattern : Twelve) (guard : d1845 pattern = 1) : d358 pattern ≤ (0 : Int) + d222 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d358, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4320 pattern childGuard
    simpa only [d1845, d358, d222, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d358, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4912 pattern childGuard
    simpa only [d1845, d358, d222, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4914 (pattern : Twelve) (guard : d0 pattern = 1) : d359 pattern ≤ (0 : Int) + d223 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4915 (pattern : Twelve) (guard : d1846 pattern = 1) : d361 pattern ≤ (0 : Int) + d228 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d361, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4913 pattern childGuard
    simpa only [d1846, d361, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d361, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4914 pattern childGuard
    simpa only [d1846, d361, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4916 (pattern : Twelve) (guard : d1845 pattern = 1) : d356 pattern ≤ (0 : Int) + d224 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4327 pattern childGuard
    simpa only [d1845, d224, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4331 pattern childGuard
    simpa only [d1845, d224, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4917 (pattern : Twelve) (guard : d0 pattern = 1) : d356 pattern ≤ (0 : Int) + d225 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4918 (pattern : Twelve) (guard : d1846 pattern = 1) : d356 pattern ≤ (0 : Int) + d229 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4916 pattern childGuard
    simpa only [d1846, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4917 pattern childGuard
    simpa only [d1846, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4919 (pattern : Twelve) (guard : d1846 pattern = 1) : d362 pattern ≤ (0 : Int) + d231 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d362, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4915 pattern childGuard
    simpa only [d362, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d362, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4918 pattern childGuard
    simpa only [d362, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4920 (pattern : Twelve) (guard : d0 pattern = 1) : d355 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4921 (pattern : Twelve) (guard : d1845 pattern = 1) : d360 pattern ≤ (0 : Int) + d226 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d360, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4335 pattern childGuard
    simpa only [d1845, d360, d226, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d360, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4920 pattern childGuard
    simpa only [d1845, d360, d226, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4922 (pattern : Twelve) (guard : d0 pattern = 1) : d360 pattern ≤ (0 : Int) + d227 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4923 (pattern : Twelve) (guard : d1846 pattern = 1) : d360 pattern ≤ (0 : Int) + d230 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4921 pattern childGuard
    simpa only [d1846, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4922 pattern childGuard
    simpa only [d1846, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4924 (pattern : Twelve) (guard : d1846 pattern = 1) : d363 pattern ≤ (0 : Int) + d232 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d363, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4923 pattern childGuard
    simpa only [d363, d232, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d363, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4918 pattern childGuard
    simpa only [d363, d232, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4925 (pattern : Twelve) (guard : d1846 pattern = 1) : d364 pattern ≤ (0 : Int) + d233 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d364, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4919 pattern childGuard
    simpa only [d364, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d364, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4924 pattern childGuard
    simpa only [d364, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4926 (pattern : Twelve) (guard : d1846 pattern = 1) : d365 pattern ≤ (0 : Int) + d234 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d365, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4925 pattern childGuard
    simpa only [d365, d234, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d365, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4924 pattern childGuard
    simpa only [d365, d234, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4927 (pattern : Twelve) (guard : d0 pattern = 1) : d1019 pattern ≤ (0 : Int) + d918 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4928 (pattern : Twelve) (guard : d1845 pattern = 1) : d1023 pattern ≤ (0 : Int) + d927 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d1023, d927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4345 pattern childGuard
    simpa only [d1845, d1023, d927, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d1023, d927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4927 pattern childGuard
    simpa only [d1845, d1023, d927, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4929 (pattern : Twelve) (guard : d0 pattern = 1) : d1024 pattern ≤ (0 : Int) + d928 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4930 (pattern : Twelve) (guard : d1846 pattern = 1) : d1025 pattern ≤ (0 : Int) + d933 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d1025, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4928 pattern childGuard
    simpa only [d1846, d1025, d933, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d1025, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4929 pattern childGuard
    simpa only [d1846, d1025, d933, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4931 (pattern : Twelve) (guard : d1845 pattern = 1) : d1022 pattern ≤ (0 : Int) + d929 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4352 pattern childGuard
    simpa only [d1845, d929, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4353 pattern childGuard
    simpa only [d1845, d929, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4932 (pattern : Twelve) (guard : d0 pattern = 1) : d1022 pattern ≤ (0 : Int) + d930 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4933 (pattern : Twelve) (guard : d1846 pattern = 1) : d1022 pattern ≤ (0 : Int) + d934 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4931 pattern childGuard
    simpa only [d1846, d934, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4932 pattern childGuard
    simpa only [d1846, d934, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4934 (pattern : Twelve) (guard : d1846 pattern = 1) : d1026 pattern ≤ (0 : Int) + d936 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1026, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4930 pattern childGuard
    simpa only [d1026, d936, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1026, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4933 pattern childGuard
    simpa only [d1026, d936, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4935 (pattern : Twelve) (guard : d1845 pattern = 1) : d1021 pattern ≤ (0 : Int) + d931 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4357 pattern childGuard
    simpa only [d1845, d931, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4358 pattern childGuard
    simpa only [d1845, d931, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4936 (pattern : Twelve) (guard : d0 pattern = 1) : d1021 pattern ≤ (0 : Int) + d932 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4937 (pattern : Twelve) (guard : d1846 pattern = 1) : d1021 pattern ≤ (0 : Int) + d935 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4935 pattern childGuard
    simpa only [d1846, d935, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4936 pattern childGuard
    simpa only [d1846, d935, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4938 (pattern : Twelve) (guard : d1846 pattern = 1) : d1027 pattern ≤ (0 : Int) + d937 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1027, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4937 pattern childGuard
    simpa only [d1027, d937, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1027, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4933 pattern childGuard
    simpa only [d1027, d937, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4939 (pattern : Twelve) (guard : d1846 pattern = 1) : d1028 pattern ≤ (0 : Int) + d938 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1028, d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4934 pattern childGuard
    simpa only [d1028, d938, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1028, d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4938 pattern childGuard
    simpa only [d1028, d938, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4940 (pattern : Twelve) (guard : d1846 pattern = 1) : d1029 pattern ≤ (0 : Int) + d939 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1029, d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4939 pattern childGuard
    simpa only [d1029, d939, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1029, d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4938 pattern childGuard
    simpa only [d1029, d939, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4941 (pattern : Twelve) (guard : d0 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1360 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4942 (pattern : Twelve) (guard : d1845 pattern = 1) : d1438 pattern ≤ (0 : Int) + d1368 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d1438, d1368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4364 pattern childGuard
    simpa only [d1845, d1438, d1368, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d1438, d1368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4941 pattern childGuard
    simpa only [d1845, d1438, d1368, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4943 (pattern : Twelve) (guard : d0 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1369 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4944 (pattern : Twelve) (guard : d1846 pattern = 1) : d1439 pattern ≤ (0 : Int) + d1373 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d1439, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4942 pattern childGuard
    simpa only [d1846, d1439, d1373, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d1439, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4943 pattern childGuard
    simpa only [d1846, d1439, d1373, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4945 (pattern : Twelve) (guard : d1845 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1370 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d1370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4371 pattern childGuard
    simpa only [d1845, d1370, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d1370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4372 pattern childGuard
    simpa only [d1845, d1370, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4946 (pattern : Twelve) (guard : d0 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1371 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4947 (pattern : Twelve) (guard : d1846 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1374 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4945 pattern childGuard
    simpa only [d1846, d1374, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4946 pattern childGuard
    simpa only [d1846, d1374, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4948 (pattern : Twelve) (guard : d1846 pattern = 1) : d1440 pattern ≤ (0 : Int) + d1376 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1440, d1376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4944 pattern childGuard
    simpa only [d1440, d1376, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1440, d1376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4947 pattern childGuard
    simpa only [d1440, d1376, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4949 (pattern : Twelve) (guard : d1845 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1372 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d1372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4366 pattern childGuard
    simpa only [d1845, d1372, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d1372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4375 pattern childGuard
    simpa only [d1845, d1372, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4950 (pattern : Twelve) (guard : d1846 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1375 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d1375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4949 pattern childGuard
    simpa only [d1846, d1375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d1375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4943 pattern childGuard
    simpa only [d1846, d1375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4951 (pattern : Twelve) (guard : d1846 pattern = 1) : d1441 pattern ≤ (0 : Int) + d1377 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1441, d1377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4950 pattern childGuard
    simpa only [d1441, d1377, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1441, d1377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4947 pattern childGuard
    simpa only [d1441, d1377, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4952 (pattern : Twelve) (guard : d1846 pattern = 1) : d1442 pattern ≤ (0 : Int) + d1378 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1442, d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4948 pattern childGuard
    simpa only [d1442, d1378, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1442, d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4951 pattern childGuard
    simpa only [d1442, d1378, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4953 (pattern : Twelve) (guard : d1846 pattern = 1) : d1443 pattern ≤ (0 : Int) + d1379 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1443, d1379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4952 pattern childGuard
    simpa only [d1443, d1379, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1846 pattern = 1 := by simpa only [d1443, d1379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4951 pattern childGuard
    simpa only [d1443, d1379, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4954 (pattern : Twelve) (guard : d1845 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1686 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1845, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4381 pattern childGuard
    simpa only [d1845, d1686, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1845, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4382 pattern childGuard
    simpa only [d1845, d1686, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4955 (pattern : Twelve) (guard : d0 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1687 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4956 (pattern : Twelve) (guard : d1846 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1688 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1845 pattern = 1 := by simpa only [d1846, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4954 pattern childGuard
    simpa only [d1846, d1688, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1846, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4955 pattern childGuard
    simpa only [d1846, d1688, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4957 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4958 (pattern : Twelve) (guard : d1848 pattern = 1) : d26 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4957 pattern childGuard
    simpa only [d1848, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4959 (pattern : Twelve) (guard : d1849 pattern = 1) : d184 pattern ≤ (0 : Int) + d235 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d184, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4958 pattern childGuard
    simpa only [d1849, d184, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d184, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1264 pattern childGuard
    simpa only [d1849, d184, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4960 (pattern : Twelve) (guard : d0 pattern = 1) : d161 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4961 (pattern : Twelve) (guard : d1848 pattern = 1) : d171 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4960 pattern childGuard
    simpa only [d1848, d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4962 (pattern : Twelve) (guard : d0 pattern = 1) : d366 pattern ≤ (0 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4963 (pattern : Twelve) (guard : d1849 pattern = 1) : d372 pattern ≤ (0 : Int) + d236 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d372, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4961 pattern childGuard
    simpa only [d1849, d372, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d372, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4962 pattern childGuard
    simpa only [d1849, d372, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4964 (pattern : Twelve) (guard : d1849 pattern = 1) : d389 pattern ≤ (0 : Int) + d256 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d389, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4959 pattern childGuard
    simpa only [d389, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d389, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4963 pattern childGuard
    simpa only [d389, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4965 (pattern : Twelve) (guard : d0 pattern = 1) : d161 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4966 (pattern : Twelve) (guard : d1848 pattern = 1) : d171 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4965 pattern childGuard
    simpa only [d1848, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4967 (pattern : Twelve) (guard : d0 pattern = 1) : d367 pattern ≤ (0 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4968 (pattern : Twelve) (guard : d1849 pattern = 1) : d373 pattern ≤ (0 : Int) + d237 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d373, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4966 pattern childGuard
    simpa only [d1849, d373, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d373, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4967 pattern childGuard
    simpa only [d1849, d373, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4969 (pattern : Twelve) (guard : d0 pattern = 1) : d163 pattern ≤ (0 : Int) + d18 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4970 (pattern : Twelve) (guard : d1848 pattern = 1) : d366 pattern ≤ (0 : Int) + d28 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d366, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d366, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d366, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4969 pattern childGuard
    simpa only [d1848, d366, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4971 (pattern : Twelve) (guard : d1849 pattern = 1) : d374 pattern ≤ (0 : Int) + d238 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d374, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4970 pattern childGuard
    simpa only [d1849, d374, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d374, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c88 pattern childGuard
    simpa only [d1849, d374, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4972 (pattern : Twelve) (guard : d1849 pattern = 1) : d390 pattern ≤ (0 : Int) + d257 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d390, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4968 pattern childGuard
    simpa only [d390, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d390, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4971 pattern childGuard
    simpa only [d390, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4973 (pattern : Twelve) (guard : d1849 pattern = 1) : d402 pattern ≤ (0 : Int) + d272 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d402, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4964 pattern childGuard
    simpa only [d402, d272, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d402, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4972 pattern childGuard
    simpa only [d402, d272, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4974 (pattern : Twelve) (guard : d0 pattern = 1) : d165 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4975 (pattern : Twelve) (guard : d1848 pattern = 1) : d368 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d368, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d368, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d368, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4974 pattern childGuard
    simpa only [d1848, d368, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4976 (pattern : Twelve) (guard : d0 pattern = 1) : d369 pattern ≤ (0 : Int) + d175 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4977 (pattern : Twelve) (guard : d1849 pattern = 1) : d375 pattern ≤ (0 : Int) + d239 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d375, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4975 pattern childGuard
    simpa only [d1849, d375, d239, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d375, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4976 pattern childGuard
    simpa only [d1849, d375, d239, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4978 (pattern : Twelve) (guard : d0 pattern = 1) : d167 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4979 (pattern : Twelve) (guard : d1848 pattern = 1) : d369 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d369, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d369, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d369, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4978 pattern childGuard
    simpa only [d1848, d369, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4980 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d176 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4981 (pattern : Twelve) (guard : d1849 pattern = 1) : d376 pattern ≤ (0 : Int) + d240 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d376, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4979 pattern childGuard
    simpa only [d1849, d376, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d376, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4980 pattern childGuard
    simpa only [d1849, d376, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4982 (pattern : Twelve) (guard : d1849 pattern = 1) : d391 pattern ≤ (0 : Int) + d258 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d391, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4977 pattern childGuard
    simpa only [d391, d258, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d391, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4981 pattern childGuard
    simpa only [d391, d258, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4983 (pattern : Twelve) (guard : d1849 pattern = 1) : d377 pattern ≤ (0 : Int) + d240 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d377, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4979 pattern childGuard
    simpa only [d1849, d377, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d377, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c247 pattern childGuard
    simpa only [d1849, d377, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4984 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4985 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d36, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4984 pattern childGuard
    simpa only [d1848, d36, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4986 (pattern : Twelve) (guard : d1849 pattern = 1) : d378 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d378, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d1849, d378, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d378, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c101 pattern childGuard
    simpa only [d1849, d378, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4987 (pattern : Twelve) (guard : d1849 pattern = 1) : d392 pattern ≤ (0 : Int) + d259 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d392, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4983 pattern childGuard
    simpa only [d392, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d392, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4986 pattern childGuard
    simpa only [d392, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4988 (pattern : Twelve) (guard : d1849 pattern = 1) : d403 pattern ≤ (0 : Int) + d273 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d403, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4982 pattern childGuard
    simpa only [d403, d273, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d403, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4987 pattern childGuard
    simpa only [d403, d273, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4989 (pattern : Twelve) (guard : d1849 pattern = 1) : d409 pattern ≤ (0 : Int) + d284 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d409, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4973 pattern childGuard
    simpa only [d409, d284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d409, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4988 pattern childGuard
    simpa only [d409, d284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4990 (pattern : Twelve) (guard : d0 pattern = 1) : d165 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4991 (pattern : Twelve) (guard : d1848 pattern = 1) : d368 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d368, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4990 pattern childGuard
    simpa only [d1848, d368, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4992 (pattern : Twelve) (guard : d1849 pattern = 1) : d375 pattern ≤ (0 : Int) + d242 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d375, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4991 pattern childGuard
    simpa only [d1849, d375, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d375, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4976 pattern childGuard
    simpa only [d1849, d375, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4993 (pattern : Twelve) (guard : d0 pattern = 1) : d167 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4994 (pattern : Twelve) (guard : d1848 pattern = 1) : d369 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d369, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d369, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d369, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4993 pattern childGuard
    simpa only [d1848, d369, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4995 (pattern : Twelve) (guard : d1849 pattern = 1) : d376 pattern ≤ (0 : Int) + d243 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d376, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4994 pattern childGuard
    simpa only [d1849, d376, d243, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d376, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4980 pattern childGuard
    simpa only [d1849, d376, d243, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4996 (pattern : Twelve) (guard : d1849 pattern = 1) : d391 pattern ≤ (0 : Int) + d260 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d391, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4992 pattern childGuard
    simpa only [d391, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d391, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4995 pattern childGuard
    simpa only [d391, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4997 (pattern : Twelve) (guard : d0 pattern = 1) : d167 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4998 (pattern : Twelve) (guard : d1848 pattern = 1) : d369 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d369, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4997 pattern childGuard
    simpa only [d1848, d369, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4999 (pattern : Twelve) (guard : d1849 pattern = 1) : d377 pattern ≤ (0 : Int) + d244 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d377, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4998 pattern childGuard
    simpa only [d1849, d377, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d377, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c247 pattern childGuard
    simpa only [d1849, d377, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5000 (pattern : Twelve) (guard : d1849 pattern = 1) : d392 pattern ≤ (0 : Int) + d261 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d392, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4999 pattern childGuard
    simpa only [d392, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d392, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4986 pattern childGuard
    simpa only [d392, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5001 (pattern : Twelve) (guard : d1849 pattern = 1) : d403 pattern ≤ (0 : Int) + d274 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d403, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4996 pattern childGuard
    simpa only [d403, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d403, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5000 pattern childGuard
    simpa only [d403, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5002 (pattern : Twelve) (guard : d0 pattern = 1) : d22 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5003 (pattern : Twelve) (guard : d1848 pattern = 1) : d33 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d33, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d33, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d33, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5002 pattern childGuard
    simpa only [d1848, d33, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5004 (pattern : Twelve) (guard : d1849 pattern = 1) : d379 pattern ≤ (0 : Int) + d245 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d379, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5003 pattern childGuard
    simpa only [d1849, d379, d245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d379, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c115 pattern childGuard
    simpa only [d1849, d379, d245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5005 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5006 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d35, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5005 pattern childGuard
    simpa only [d1848, d35, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5007 (pattern : Twelve) (guard : d1849 pattern = 1) : d380 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d380, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1849, d380, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d380, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c117 pattern childGuard
    simpa only [d1849, d380, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5008 (pattern : Twelve) (guard : d1849 pattern = 1) : d393 pattern ≤ (0 : Int) + d262 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d393, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5004 pattern childGuard
    simpa only [d393, d262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d393, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5007 pattern childGuard
    simpa only [d393, d262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5009 (pattern : Twelve) (guard : d1849 pattern = 1) : d35 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c120 pattern childGuard
    simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5010 (pattern : Twelve) (guard : d1849 pattern = 1) : d394 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d394, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5009 pattern childGuard
    simpa only [d394, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d394, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4986 pattern childGuard
    simpa only [d394, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5011 (pattern : Twelve) (guard : d1849 pattern = 1) : d404 pattern ≤ (0 : Int) + d275 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d404, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5008 pattern childGuard
    simpa only [d404, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d404, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5010 pattern childGuard
    simpa only [d404, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5012 (pattern : Twelve) (guard : d1849 pattern = 1) : d410 pattern ≤ (0 : Int) + d285 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d410, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5001 pattern childGuard
    simpa only [d410, d285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d410, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5011 pattern childGuard
    simpa only [d410, d285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5013 (pattern : Twelve) (guard : d1849 pattern = 1) : d415 pattern ≤ (0 : Int) + d293 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d415, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4989 pattern childGuard
    simpa only [d415, d293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d415, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5012 pattern childGuard
    simpa only [d415, d293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5014 (pattern : Twelve) (guard : d0 pattern = 1) : d169 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5015 (pattern : Twelve) (guard : d1848 pattern = 1) : d370 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d370, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d370, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d370, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5014 pattern childGuard
    simpa only [d1848, d370, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5016 (pattern : Twelve) (guard : d0 pattern = 1) : d371 pattern ≤ (0 : Int) + d180 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5017 (pattern : Twelve) (guard : d1849 pattern = 1) : d381 pattern ≤ (0 : Int) + d247 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d381, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5015 pattern childGuard
    simpa only [d1849, d381, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d381, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5016 pattern childGuard
    simpa only [d1849, d381, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5018 (pattern : Twelve) (guard : d0 pattern = 1) : d170 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5019 (pattern : Twelve) (guard : d1848 pattern = 1) : d371 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d371, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d371, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d371, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5018 pattern childGuard
    simpa only [d1848, d371, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5020 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d181 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5021 (pattern : Twelve) (guard : d1849 pattern = 1) : d382 pattern ≤ (0 : Int) + d248 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d382, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5019 pattern childGuard
    simpa only [d1849, d382, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d382, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5020 pattern childGuard
    simpa only [d1849, d382, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5022 (pattern : Twelve) (guard : d1849 pattern = 1) : d395 pattern ≤ (0 : Int) + d264 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d395, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5017 pattern childGuard
    simpa only [d395, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d395, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5021 pattern childGuard
    simpa only [d395, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5023 (pattern : Twelve) (guard : d0 pattern = 1) : d35 pattern ≤ (0 : Int) + d181 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5024 (pattern : Twelve) (guard : d1849 pattern = 1) : d383 pattern ≤ (0 : Int) + d248 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d383, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5019 pattern childGuard
    simpa only [d1849, d383, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d383, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5023 pattern childGuard
    simpa only [d1849, d383, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5025 (pattern : Twelve) (guard : d1849 pattern = 1) : d396 pattern ≤ (0 : Int) + d265 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d396, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5024 pattern childGuard
    simpa only [d396, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d396, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4986 pattern childGuard
    simpa only [d396, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5026 (pattern : Twelve) (guard : d1849 pattern = 1) : d405 pattern ≤ (0 : Int) + d276 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d405, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5022 pattern childGuard
    simpa only [d405, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d405, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5025 pattern childGuard
    simpa only [d405, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5027 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5028 (pattern : Twelve) (guard : d1848 pattern = 1) : d39 pattern ≤ (0 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d39, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1848, d39, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d39, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d1848, d39, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5029 (pattern : Twelve) (guard : d1849 pattern = 1) : d39 pattern ≤ (0 : Int) + d249 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5028 pattern childGuard
    simpa only [d1849, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c136 pattern childGuard
    simpa only [d1849, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5030 (pattern : Twelve) (guard : d1849 pattern = 1) : d384 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d384, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5028 pattern childGuard
    simpa only [d1849, d384, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d384, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c138 pattern childGuard
    simpa only [d1849, d384, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5031 (pattern : Twelve) (guard : d1849 pattern = 1) : d397 pattern ≤ (0 : Int) + d266 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d397, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5029 pattern childGuard
    simpa only [d397, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d397, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5030 pattern childGuard
    simpa only [d397, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5032 (pattern : Twelve) (guard : d1849 pattern = 1) : d39 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5028 pattern childGuard
    simpa only [d1849, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c141 pattern childGuard
    simpa only [d1849, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5033 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d24 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5034 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (0 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d40, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1340 pattern childGuard
    simpa only [d1848, d40, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d40, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5033 pattern childGuard
    simpa only [d1848, d40, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5035 (pattern : Twelve) (guard : d1849 pattern = 1) : d385 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d385, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5034 pattern childGuard
    simpa only [d1849, d385, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d385, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c144 pattern childGuard
    simpa only [d1849, d385, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5036 (pattern : Twelve) (guard : d1849 pattern = 1) : d398 pattern ≤ (0 : Int) + d267 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d398, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5032 pattern childGuard
    simpa only [d398, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d398, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5035 pattern childGuard
    simpa only [d398, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5037 (pattern : Twelve) (guard : d1849 pattern = 1) : d406 pattern ≤ (0 : Int) + d277 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d406, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5031 pattern childGuard
    simpa only [d406, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d406, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5036 pattern childGuard
    simpa only [d406, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5038 (pattern : Twelve) (guard : d1849 pattern = 1) : d411 pattern ≤ (0 : Int) + d286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d411, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5026 pattern childGuard
    simpa only [d411, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d411, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5037 pattern childGuard
    simpa only [d411, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5039 (pattern : Twelve) (guard : d1849 pattern = 1) : d35 pattern ≤ (0 : Int) + d252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1849, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c149 pattern childGuard
    simpa only [d1849, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
