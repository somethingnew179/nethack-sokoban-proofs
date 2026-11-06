/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons098
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c13860 (pattern : Twelve) (guard : d1844 pattern = 1) : d359 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d359, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13859 pattern childGuard
    simpa only [d359, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d359, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4337 pattern childGuard
    simpa only [d359, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13861 (pattern : Twelve) (guard : d2270 pattern = 1) : d361 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13857 pattern childGuard
    simpa only [d2270, d361, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13860 pattern childGuard
    simpa only [d2270, d361, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13862 (pattern : Twelve) (guard : d0 pattern = 1) : d356 pattern ≤ (0 : Int) + d112 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13863 (pattern : Twelve) (guard : d2270 pattern = 1) : d356 pattern ≤ (0 : Int) + d112 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13862 pattern childGuard
    simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4330 pattern childGuard
    simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13864 (pattern : Twelve) (guard : d2270 pattern = 1) : d362 pattern ≤ (0 : Int) + d2276 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2270 pattern = 1 := by simpa only [d362, d2276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13861 pattern childGuard
    simpa only [d362, d2276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2270 pattern = 1 := by simpa only [d362, d2276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13863 pattern childGuard
    simpa only [d362, d2276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13865 (pattern : Twelve) (guard : d0 pattern = 1) : d360 pattern ≤ (0 : Int) + d110 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13866 (pattern : Twelve) (guard : d2270 pattern = 1) : d360 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13865 pattern childGuard
    simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4338 pattern childGuard
    simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13867 (pattern : Twelve) (guard : d2270 pattern = 1) : d363 pattern ≤ (0 : Int) + d2276 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2270 pattern = 1 := by simpa only [d363, d2276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13866 pattern childGuard
    simpa only [d363, d2276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2270 pattern = 1 := by simpa only [d363, d2276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13863 pattern childGuard
    simpa only [d363, d2276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13868 (pattern : Twelve) (guard : d2270 pattern = 1) : d364 pattern ≤ (0 : Int) + d2276 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2270 pattern = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13864 pattern childGuard
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2270 pattern = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13867 pattern childGuard
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13869 (pattern : Twelve) (guard : d2270 pattern = 1) : d365 pattern ≤ (0 : Int) + d2276 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2270 pattern = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13868 pattern childGuard
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2270 pattern = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13867 pattern childGuard
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13870 (pattern : Twelve) (guard : d0 pattern = 1) : d1023 pattern ≤ (0 : Int) + d861 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13871 (pattern : Twelve) (guard : d0 pattern = 1) : d916 pattern ≤ (0 : Int) + d854 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13872 (pattern : Twelve) (guard : d1844 pattern = 1) : d1020 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1020, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c756 pattern childGuard
    simpa only [d1844, d1020, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1020, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13871 pattern childGuard
    simpa only [d1844, d1020, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13873 (pattern : Twelve) (guard : d1844 pattern = 1) : d1024 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13872 pattern childGuard
    simpa only [d1024, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4357 pattern childGuard
    simpa only [d1024, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13874 (pattern : Twelve) (guard : d2270 pattern = 1) : d1025 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13870 pattern childGuard
    simpa only [d2270, d1025, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13873 pattern childGuard
    simpa only [d2270, d1025, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13875 (pattern : Twelve) (guard : d0 pattern = 1) : d1022 pattern ≤ (0 : Int) + d864 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13876 (pattern : Twelve) (guard : d2270 pattern = 1) : d1022 pattern ≤ (0 : Int) + d864 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13875 pattern childGuard
    simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4352 pattern childGuard
    simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13877 (pattern : Twelve) (guard : d2270 pattern = 1) : d1026 pattern ≤ (0 : Int) + d2268 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1026, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13874 pattern childGuard
    simpa only [d1026, d2268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1026, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13876 pattern childGuard
    simpa only [d1026, d2268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13878 (pattern : Twelve) (guard : d0 pattern = 1) : d1021 pattern ≤ (0 : Int) + d861 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13879 (pattern : Twelve) (guard : d2270 pattern = 1) : d1021 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13878 pattern childGuard
    simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4357 pattern childGuard
    simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13880 (pattern : Twelve) (guard : d2270 pattern = 1) : d1027 pattern ≤ (0 : Int) + d2268 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1027, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13879 pattern childGuard
    simpa only [d1027, d2268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1027, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13876 pattern childGuard
    simpa only [d1027, d2268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13881 (pattern : Twelve) (guard : d2270 pattern = 1) : d1028 pattern ≤ (0 : Int) + d2268 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13877 pattern childGuard
    simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13880 pattern childGuard
    simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13882 (pattern : Twelve) (guard : d2270 pattern = 1) : d1029 pattern ≤ (0 : Int) + d2268 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13881 pattern childGuard
    simpa only [d1029, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13880 pattern childGuard
    simpa only [d1029, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13883 (pattern : Twelve) (guard : d0 pattern = 1) : d1438 pattern ≤ (0 : Int) + d1313 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13884 (pattern : Twelve) (guard : d2270 pattern = 1) : d1439 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13883 pattern childGuard
    simpa only [d2270, d1439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4366 pattern childGuard
    simpa only [d2270, d1439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13885 (pattern : Twelve) (guard : d0 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1316 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13886 (pattern : Twelve) (guard : d2270 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1316 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13885 pattern childGuard
    simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4371 pattern childGuard
    simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13887 (pattern : Twelve) (guard : d2270 pattern = 1) : d1440 pattern ≤ (0 : Int) + d2269 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1440, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13884 pattern childGuard
    simpa only [d1440, d2269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1440, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13886 pattern childGuard
    simpa only [d1440, d2269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13888 (pattern : Twelve) (guard : d0 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1313 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13889 (pattern : Twelve) (guard : d2270 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13888 pattern childGuard
    simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4366 pattern childGuard
    simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13890 (pattern : Twelve) (guard : d2270 pattern = 1) : d1441 pattern ≤ (0 : Int) + d2269 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1441, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13889 pattern childGuard
    simpa only [d1441, d2269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1441, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13886 pattern childGuard
    simpa only [d1441, d2269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13891 (pattern : Twelve) (guard : d2270 pattern = 1) : d1442 pattern ≤ (0 : Int) + d2269 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13887 pattern childGuard
    simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13890 pattern childGuard
    simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13892 (pattern : Twelve) (guard : d2270 pattern = 1) : d1443 pattern ≤ (0 : Int) + d2269 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13891 pattern childGuard
    simpa only [d1443, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2270 pattern = 1 := by simpa only [d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13890 pattern childGuard
    simpa only [d1443, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13893 (pattern : Twelve) (guard : d0 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1660 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13894 (pattern : Twelve) (guard : d2270 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1660 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13893 pattern childGuard
    simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4381 pattern childGuard
    simpa only [d2270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13895 (pattern : Twelve) (guard : d0 pattern = 1) : d91 pattern ≤ (2 : Int) + d2283 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13896 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13897 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13896 pattern childGuard
    simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13898 (pattern : Twelve) (guard : d0 pattern = 1) : d20 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13899 (pattern : Twelve) (guard : d1848 pattern = 1) : d31 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d1848, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13898 pattern childGuard
    simpa only [d1848, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13900 (pattern : Twelve) (guard : d1848 pattern = 1) : d52 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13897 pattern childGuard
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13899 pattern childGuard
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13901 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d1 pattern := by
  change (0 : Int) ≤ (2 : Int) + 1
  decide
theorem c13902 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (2 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13903 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13901 pattern childGuard
    simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13902 pattern childGuard
    simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13904 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13901 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13320 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13905 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13901 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13904 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13906 (pattern : Twelve) (guard : d0 pattern = 1) : d21 pattern ≤ (2 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13907 (pattern : Twelve) (guard : d1848 pattern = 1) : d32 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13905 pattern childGuard
    simpa only [d1848, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13906 pattern childGuard
    simpa only [d1848, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13908 (pattern : Twelve) (guard : d1848 pattern = 1) : d53 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13903 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13907 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13909 (pattern : Twelve) (guard : d1848 pattern = 1) : d74 pattern ≤ (2 : Int) + d1859 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d74, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13900 pattern childGuard
    simpa only [d74, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d74, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13908 pattern childGuard
    simpa only [d74, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13910 (pattern : Twelve) (guard : d0 pattern = 1) : d22 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13911 (pattern : Twelve) (guard : d1848 pattern = 1) : d33 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d1848, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13910 pattern childGuard
    simpa only [d1848, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13912 (pattern : Twelve) (guard : d1848 pattern = 1) : d54 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13897 pattern childGuard
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13911 pattern childGuard
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13913 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d2 pattern := by
  change (0 : Int) ≤ (2 : Int) + 2
  decide
theorem c13914 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13901 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13915 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d3 pattern := by
  change (1 : Int) ≤ (2 : Int) + 3
  decide
theorem c13916 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (2 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d7, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d7, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13917 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (2 : Int) + d18 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13914 pattern childGuard
    simpa only [d17, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13916 pattern childGuard
    simpa only [d17, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13918 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (2 : Int) + d18 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13919 (pattern : Twelve) (guard : d1848 pattern = 1) : d34 pattern ≤ (2 : Int) + d18 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13917 pattern childGuard
    simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13918 pattern childGuard
    simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13920 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d6 pattern := by
  change (0 : Int) ≤ (2 : Int) + 6
  decide
theorem c13921 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13920 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13483 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13922 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d6 pattern := by
  change (1 : Int) ≤ (2 : Int) + 6
  decide
theorem c13923 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13922 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13489 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13924 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13921 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13923 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13925 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13926 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13924 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13927 (pattern : Twelve) (guard : d1848 pattern = 1) : d55 pattern ≤ (2 : Int) + d2281 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d55, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13919 pattern childGuard
    simpa only [d55, d2281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d55, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13926 pattern childGuard
    simpa only [d55, d2281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13928 (pattern : Twelve) (guard : d1848 pattern = 1) : d75 pattern ≤ (2 : Int) + d2282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d75, d2282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13912 pattern childGuard
    simpa only [d75, d2282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d75, d2282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13927 pattern childGuard
    simpa only [d75, d2282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13929 (pattern : Twelve) (guard : d1848 pattern = 1) : d92 pattern ≤ (2 : Int) + d2283 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d92, d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13909 pattern childGuard
    simpa only [d92, d2283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d92, d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13928 pattern childGuard
    simpa only [d92, d2283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13930 (pattern : Twelve) (guard : d2279 pattern = 1) : d102 pattern ≤ (2 : Int) + d2283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13895 pattern childGuard
    simpa only [d2279, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13929 pattern childGuard
    simpa only [d2279, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13931 (pattern : Twelve) (guard : d0 pattern = 1) : d93 pattern ≤ (2 : Int) + d2286 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13932 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13933 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13932 pattern childGuard
    simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13934 (pattern : Twelve) (guard : d1848 pattern = 1) : d56 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13897 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13933 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13935 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13936 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13905 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13935 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13937 (pattern : Twelve) (guard : d1848 pattern = 1) : d57 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13903 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13936 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13938 (pattern : Twelve) (guard : d1848 pattern = 1) : d77 pattern ≤ (2 : Int) + d1859 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d77, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13934 pattern childGuard
    simpa only [d77, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d77, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13937 pattern childGuard
    simpa only [d77, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13939 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13916 pattern childGuard
    simpa only [d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13940 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (2 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13941 (pattern : Twelve) (guard : d1848 pattern = 1) : d34 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13939 pattern childGuard
    simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13940 pattern childGuard
    simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13942 (pattern : Twelve) (guard : d1848 pattern = 1) : d55 pattern ≤ (2 : Int) + d2284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d55, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13941 pattern childGuard
    simpa only [d55, d2284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d55, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13926 pattern childGuard
    simpa only [d55, d2284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13943 (pattern : Twelve) (guard : d1848 pattern = 1) : d78 pattern ≤ (2 : Int) + d2285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d78, d2285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13934 pattern childGuard
    simpa only [d78, d2285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d78, d2285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13942 pattern childGuard
    simpa only [d78, d2285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13944 (pattern : Twelve) (guard : d1848 pattern = 1) : d94 pattern ≤ (2 : Int) + d2286 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d94, d2286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13938 pattern childGuard
    simpa only [d94, d2286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d94, d2286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13943 pattern childGuard
    simpa only [d94, d2286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13945 (pattern : Twelve) (guard : d2279 pattern = 1) : d103 pattern ≤ (2 : Int) + d2286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13931 pattern childGuard
    simpa only [d2279, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13944 pattern childGuard
    simpa only [d2279, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13946 (pattern : Twelve) (guard : d2279 pattern = 1) : d110 pattern ≤ (2 : Int) + d2287 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d110, d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13930 pattern childGuard
    simpa only [d110, d2287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2279 pattern = 1 := by simpa only [d110, d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13945 pattern childGuard
    simpa only [d110, d2287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13947 (pattern : Twelve) (guard : d0 pattern = 1) : d217 pattern ≤ (2 : Int) + d2287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13948 (pattern : Twelve) (guard : d2280 pattern = 1) : d345 pattern ≤ (2 : Int) + d2287 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13946 pattern childGuard
    simpa only [d2280, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13947 pattern childGuard
    simpa only [d2280, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13949 (pattern : Twelve) (guard : d0 pattern = 1) : d97 pattern ≤ (2 : Int) + d2289 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13950 (pattern : Twelve) (guard : d1848 pattern = 1) : d43 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13320 pattern childGuard
    simpa only [d1848, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13906 pattern childGuard
    simpa only [d1848, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13951 (pattern : Twelve) (guard : d1848 pattern = 1) : d62 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13903 pattern childGuard
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13950 pattern childGuard
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13952 (pattern : Twelve) (guard : d1848 pattern = 1) : d83 pattern ≤ (2 : Int) + d1859 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d83, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13900 pattern childGuard
    simpa only [d83, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d83, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13951 pattern childGuard
    simpa only [d83, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13953 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (2 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13954 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13953 pattern childGuard
    simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13955 (pattern : Twelve) (guard : d0 pattern = 1) : d22 pattern ≤ (2 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13956 (pattern : Twelve) (guard : d1848 pattern = 1) : d44 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d1848, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13955 pattern childGuard
    simpa only [d1848, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13957 (pattern : Twelve) (guard : d1848 pattern = 1) : d63 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13954 pattern childGuard
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13956 pattern childGuard
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13958 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13538 pattern childGuard
    simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13959 (pattern : Twelve) (guard : d1848 pattern = 1) : d64 pattern ≤ (2 : Int) + d2284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d64, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13941 pattern childGuard
    simpa only [d64, d2284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d64, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13958 pattern childGuard
    simpa only [d64, d2284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13960 (pattern : Twelve) (guard : d1848 pattern = 1) : d84 pattern ≤ (2 : Int) + d2288 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d84, d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13957 pattern childGuard
    simpa only [d84, d2288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d84, d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13959 pattern childGuard
    simpa only [d84, d2288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13961 (pattern : Twelve) (guard : d1848 pattern = 1) : d98 pattern ≤ (2 : Int) + d2289 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d98, d2289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13952 pattern childGuard
    simpa only [d98, d2289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d98, d2289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13960 pattern childGuard
    simpa only [d98, d2289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13962 (pattern : Twelve) (guard : d2279 pattern = 1) : d106 pattern ≤ (2 : Int) + d2289 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13949 pattern childGuard
    simpa only [d2279, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13961 pattern childGuard
    simpa only [d2279, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13963 (pattern : Twelve) (guard : d1848 pattern = 1) : d45 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13320 pattern childGuard
    simpa only [d1848, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13935 pattern childGuard
    simpa only [d1848, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13964 (pattern : Twelve) (guard : d1848 pattern = 1) : d65 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13903 pattern childGuard
    simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13963 pattern childGuard
    simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13965 (pattern : Twelve) (guard : d1848 pattern = 1) : d85 pattern ≤ (2 : Int) + d1859 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d85, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13934 pattern childGuard
    simpa only [d85, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d85, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13964 pattern childGuard
    simpa only [d85, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13966 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13967 (pattern : Twelve) (guard : d1848 pattern = 1) : d39 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13966 pattern childGuard
    simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13968 (pattern : Twelve) (guard : d1848 pattern = 1) : d66 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13954 pattern childGuard
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13967 pattern childGuard
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13969 (pattern : Twelve) (guard : d1848 pattern = 1) : d86 pattern ≤ (2 : Int) + d2288 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d86, d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13968 pattern childGuard
    simpa only [d86, d2288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d86, d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13959 pattern childGuard
    simpa only [d86, d2288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13970 (pattern : Twelve) (guard : d1848 pattern = 1) : d99 pattern ≤ (2 : Int) + d2289 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d99, d2289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13965 pattern childGuard
    simpa only [d99, d2289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d99, d2289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13969 pattern childGuard
    simpa only [d99, d2289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13971 (pattern : Twelve) (guard : d2279 pattern = 1) : d107 pattern ≤ (2 : Int) + d2289 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13949 pattern childGuard
    simpa only [d2279, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13970 pattern childGuard
    simpa only [d2279, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13972 (pattern : Twelve) (guard : d2279 pattern = 1) : d112 pattern ≤ (2 : Int) + d2289 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13962 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2279 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13971 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13973 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2289 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13974 (pattern : Twelve) (guard : d2280 pattern = 1) : d346 pattern ≤ (2 : Int) + d2289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13972 pattern childGuard
    simpa only [d2280, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13973 pattern childGuard
    simpa only [d2280, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13975 (pattern : Twelve) (guard : d2280 pattern = 1) : d348 pattern ≤ (2 : Int) + d2290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d348, d2290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13948 pattern childGuard
    simpa only [d348, d2290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d348, d2290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13974 pattern childGuard
    simpa only [d348, d2290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13976 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13977 (pattern : Twelve) (guard : d2280 pattern = 1) : d347 pattern ≤ (2 : Int) + d2287 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13946 pattern childGuard
    simpa only [d2280, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13976 pattern childGuard
    simpa only [d2280, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13978 (pattern : Twelve) (guard : d2280 pattern = 1) : d349 pattern ≤ (2 : Int) + d2290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d349, d2290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13977 pattern childGuard
    simpa only [d349, d2290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d349, d2290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13974 pattern childGuard
    simpa only [d349, d2290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13979 (pattern : Twelve) (guard : d2280 pattern = 1) : d350 pattern ≤ (2 : Int) + d2290 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13975 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13978 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13980 (pattern : Twelve) (guard : d2280 pattern = 1) : d351 pattern ≤ (2 : Int) + d2290 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13979 pattern childGuard
    simpa only [d351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13978 pattern childGuard
    simpa only [d351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13981 (pattern : Twelve) (guard : d0 pattern = 1) : d853 pattern ≤ (2 : Int) + d2292 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13982 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (2 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13983 (pattern : Twelve) (guard : d1848 pattern = 1) : d34 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13905 pattern childGuard
    simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13982 pattern childGuard
    simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13984 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13904 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13320 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13985 (pattern : Twelve) (guard : d1848 pattern = 1) : d818 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13984 pattern childGuard
    simpa only [d1848, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13935 pattern childGuard
    simpa only [d1848, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13986 (pattern : Twelve) (guard : d1848 pattern = 1) : d826 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13983 pattern childGuard
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13985 pattern childGuard
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13987 (pattern : Twelve) (guard : d1848 pattern = 1) : d840 pattern ≤ (2 : Int) + d1859 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d840, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13934 pattern childGuard
    simpa only [d840, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d840, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13986 pattern childGuard
    simpa only [d840, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13988 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (2 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13989 (pattern : Twelve) (guard : d1848 pattern = 1) : d34 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13988 pattern childGuard
    simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13990 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13991 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13990 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13992 (pattern : Twelve) (guard : d1848 pattern = 1) : d827 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13989 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13991 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13993 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13994 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (2 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13491 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13995 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13993 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13994 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13996 (pattern : Twelve) (guard : d0 pattern = 1) : d25 pattern ≤ (2 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13997 (pattern : Twelve) (guard : d1848 pattern = 1) : d817 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13995 pattern childGuard
    simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13996 pattern childGuard
    simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13998 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13577 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13999 (pattern : Twelve) (guard : d1848 pattern = 1) : d825 pattern ≤ (2 : Int) + d1690 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d825, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13997 pattern childGuard
    simpa only [d825, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d825, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13998 pattern childGuard
    simpa only [d825, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
