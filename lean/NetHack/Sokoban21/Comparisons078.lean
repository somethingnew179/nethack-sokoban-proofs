/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons077
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c10920 (pattern : Twelve) (guard : d1 pattern = 1) : d64 pattern ≤ (0 : Int) + d71 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10887 pattern childGuard
    simpa only [d64, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10919 pattern childGuard
    simpa only [d64, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10921 (pattern : Twelve) (guard : d1 pattern = 1) : d86 pattern ≤ (0 : Int) + d90 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10918 pattern childGuard
    simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10920 pattern childGuard
    simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10922 (pattern : Twelve) (guard : d1 pattern = 1) : d99 pattern ≤ (0 : Int) + d101 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10916 pattern childGuard
    simpa only [d99, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10921 pattern childGuard
    simpa only [d99, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10923 (pattern : Twelve) (guard : d1 pattern = 1) : d107 pattern ≤ (0 : Int) + d108 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10913 pattern childGuard
    simpa only [d107, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10922 pattern childGuard
    simpa only [d107, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10924 (pattern : Twelve) (guard : d1836 pattern = 1) : d112 pattern ≤ (0 : Int) + d108 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1836, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10899 pattern childGuard
    simpa only [d1836, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1836, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10923 pattern childGuard
    simpa only [d1836, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10925 (pattern : Twelve) (guard : d0 pattern = 1) : d113 pattern ≤ (0 : Int) + d108 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10926 (pattern : Twelve) (guard : d1890 pattern = 1) : d115 pattern ≤ (0 : Int) + d108 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10924 pattern childGuard
    simpa only [d1890, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10925 pattern childGuard
    simpa only [d1890, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10927 (pattern : Twelve) (guard : d1890 pattern = 1) : d116 pattern ≤ (0 : Int) + d1898 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1890 pattern = 1 := by simpa only [d116, d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10898 pattern childGuard
    simpa only [d116, d1898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1890 pattern = 1 := by simpa only [d116, d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10926 pattern childGuard
    simpa only [d116, d1898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10928 (pattern : Twelve) (guard : d0 pattern = 1) : d861 pattern ≤ (0 : Int) + d862 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10929 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10865 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10867 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10930 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10865 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10929 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10931 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d27, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10930 pattern childGuard
    simpa only [d27, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10932 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (0 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d816, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10867 pattern childGuard
    simpa only [d816, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10933 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (0 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10931 pattern childGuard
    simpa only [d824, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10932 pattern childGuard
    simpa only [d824, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10934 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (0 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10864 pattern childGuard
    simpa only [d838, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10933 pattern childGuard
    simpa only [d838, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10935 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10880 pattern childGuard
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10936 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (0 : Int) + d825 pattern := by
  omega
theorem c10937 (pattern : Twelve) (guard : d1 pattern = 1) : d839 pattern ≤ (0 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10935 pattern childGuard
    simpa only [d839, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10936 pattern childGuard
    simpa only [d839, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10938 (pattern : Twelve) (guard : d1 pattern = 1) : d853 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10934 pattern childGuard
    simpa only [d853, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10937 pattern childGuard
    simpa only [d853, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10939 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10879 pattern childGuard
    simpa only [d814, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10867 pattern childGuard
    simpa only [d814, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10940 (pattern : Twelve) (guard : d1 pattern = 1) : d818 pattern ≤ (0 : Int) + d820 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10939 pattern childGuard
    simpa only [d818, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d818, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10941 (pattern : Twelve) (guard : d1 pattern = 1) : d826 pattern ≤ (0 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10887 pattern childGuard
    simpa only [d826, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10940 pattern childGuard
    simpa only [d826, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10942 (pattern : Twelve) (guard : d1 pattern = 1) : d840 pattern ≤ (0 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10878 pattern childGuard
    simpa only [d840, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10941 pattern childGuard
    simpa only [d840, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10943 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (0 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10887 pattern childGuard
    simpa only [d827, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10881 pattern childGuard
    simpa only [d827, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10944 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (0 : Int) + d6 pattern := by
  change (4 : Int) ≤ (0 : Int) + 6
  decide
theorem c10945 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (0 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10944 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10946 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (0 : Int) + d6 pattern := by
  change (5 : Int) ≤ (0 : Int) + 6
  decide
theorem c10947 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10884 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10946 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10948 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10945 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10947 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10949 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (0 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10890 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10948 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10950 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (0 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10948 pattern childGuard
    simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10951 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (0 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10949 pattern childGuard
    simpa only [d825, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10950 pattern childGuard
    simpa only [d825, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10952 (pattern : Twelve) (guard : d1 pattern = 1) : d841 pattern ≤ (0 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10943 pattern childGuard
    simpa only [d841, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10951 pattern childGuard
    simpa only [d841, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10953 (pattern : Twelve) (guard : d1 pattern = 1) : d854 pattern ≤ (0 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10942 pattern childGuard
    simpa only [d854, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10952 pattern childGuard
    simpa only [d854, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10954 (pattern : Twelve) (guard : d1 pattern = 1) : d861 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10938 pattern childGuard
    simpa only [d861, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10953 pattern childGuard
    simpa only [d861, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10955 (pattern : Twelve) (guard : d1836 pattern = 1) : d861 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10928 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10954 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10956 (pattern : Twelve) (guard : d0 pattern = 1) : d867 pattern ≤ (0 : Int) + d862 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10957 (pattern : Twelve) (guard : d1890 pattern = 1) : d869 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10955 pattern childGuard
    simpa only [d1890, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10956 pattern childGuard
    simpa only [d1890, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10958 (pattern : Twelve) (guard : d0 pattern = 1) : d864 pattern ≤ (0 : Int) + d865 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10959 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10901 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10960 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (0 : Int) + d46 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10959 pattern childGuard
    simpa only [d816, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10867 pattern childGuard
    simpa only [d816, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10961 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (0 : Int) + d834 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10931 pattern childGuard
    simpa only [d824, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10960 pattern childGuard
    simpa only [d824, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10962 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (0 : Int) + d849 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10864 pattern childGuard
    simpa only [d838, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10961 pattern childGuard
    simpa only [d838, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10963 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (0 : Int) + d3 pattern := by
  change (2 : Int) ≤ (0 : Int) + 3
  decide
theorem c10964 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10963 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10965 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10964 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10966 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d823, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10965 pattern childGuard
    simpa only [d823, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10967 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10865 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10968 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10967 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10969 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (0 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10968 pattern childGuard
    simpa only [d823, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d823, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10970 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (0 : Int) + d835 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10966 pattern childGuard
    simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10969 pattern childGuard
    simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10971 (pattern : Twelve) (guard : d1 pattern = 1) : d846 pattern ≤ (0 : Int) + d850 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10970 pattern childGuard
    simpa only [d846, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10936 pattern childGuard
    simpa only [d846, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10972 (pattern : Twelve) (guard : d1 pattern = 1) : d857 pattern ≤ (0 : Int) + d859 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10962 pattern childGuard
    simpa only [d857, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10971 pattern childGuard
    simpa only [d857, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10973 (pattern : Twelve) (guard : d1 pattern = 1) : d832 pattern ≤ (0 : Int) + d836 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10887 pattern childGuard
    simpa only [d832, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10914 pattern childGuard
    simpa only [d832, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10974 (pattern : Twelve) (guard : d1 pattern = 1) : d847 pattern ≤ (0 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10878 pattern childGuard
    simpa only [d847, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10973 pattern childGuard
    simpa only [d847, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10975 (pattern : Twelve) (guard : d1 pattern = 1) : d833 pattern ≤ (0 : Int) + d837 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10887 pattern childGuard
    simpa only [d833, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10917 pattern childGuard
    simpa only [d833, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10976 (pattern : Twelve) (guard : d1 pattern = 1) : d848 pattern ≤ (0 : Int) + d852 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10975 pattern childGuard
    simpa only [d848, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10951 pattern childGuard
    simpa only [d848, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10977 (pattern : Twelve) (guard : d1 pattern = 1) : d858 pattern ≤ (0 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10974 pattern childGuard
    simpa only [d858, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10976 pattern childGuard
    simpa only [d858, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10978 (pattern : Twelve) (guard : d1 pattern = 1) : d864 pattern ≤ (0 : Int) + d865 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10972 pattern childGuard
    simpa only [d864, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10977 pattern childGuard
    simpa only [d864, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10979 (pattern : Twelve) (guard : d1836 pattern = 1) : d864 pattern ≤ (0 : Int) + d865 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10958 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10978 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10980 (pattern : Twelve) (guard : d0 pattern = 1) : d868 pattern ≤ (0 : Int) + d865 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10981 (pattern : Twelve) (guard : d1890 pattern = 1) : d870 pattern ≤ (0 : Int) + d865 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10979 pattern childGuard
    simpa only [d1890, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10980 pattern childGuard
    simpa only [d1890, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10982 (pattern : Twelve) (guard : d1890 pattern = 1) : d871 pattern ≤ (0 : Int) + d1899 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1890 pattern = 1 := by simpa only [d871, d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10957 pattern childGuard
    simpa only [d871, d1899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1890 pattern = 1 := by simpa only [d871, d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10981 pattern childGuard
    simpa only [d871, d1899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10983 (pattern : Twelve) (guard : d0 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1314 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10984 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (0 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10867 pattern childGuard
    simpa only [d8, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d8, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10985 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (0 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10929 pattern childGuard
    simpa only [d872, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10984 pattern childGuard
    simpa only [d872, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10986 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (0 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1469 pattern childGuard
    simpa only [d1278, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10985 pattern childGuard
    simpa only [d1278, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10987 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (0 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10867 pattern childGuard
    simpa only [d872, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10984 pattern childGuard
    simpa only [d872, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10988 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (0 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4265 pattern childGuard
    simpa only [d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10987 pattern childGuard
    simpa only [d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10989 (pattern : Twelve) (guard : d1 pattern = 1) : d1284 pattern ≤ (0 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10986 pattern childGuard
    simpa only [d1284, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10988 pattern childGuard
    simpa only [d1284, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10990 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10935 pattern childGuard
    simpa only [d1293, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10989 pattern childGuard
    simpa only [d1293, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10991 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (0 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10890 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10992 (pattern : Twelve) (guard : d1 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10991 pattern childGuard
    simpa only [d1294, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d1294, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10993 (pattern : Twelve) (guard : d1 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10990 pattern childGuard
    simpa only [d1305, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10992 pattern childGuard
    simpa only [d1305, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10994 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (0 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10879 pattern childGuard
    simpa only [d1275, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10984 pattern childGuard
    simpa only [d1275, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10995 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10884 pattern childGuard
    simpa only [d117, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10944 pattern childGuard
    simpa only [d117, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10996 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (0 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10885 pattern childGuard
    simpa only [d1276, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10995 pattern childGuard
    simpa only [d1276, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10997 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (0 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10994 pattern childGuard
    simpa only [d1279, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10996 pattern childGuard
    simpa only [d1279, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10998 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (0 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10987 pattern childGuard
    simpa only [d1280, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d1280, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10999 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (0 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10997 pattern childGuard
    simpa only [d1285, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10998 pattern childGuard
    simpa only [d1285, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11000 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (0 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10943 pattern childGuard
    simpa only [d1295, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10999 pattern childGuard
    simpa only [d1295, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11001 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (0 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10949 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10891 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11002 (pattern : Twelve) (guard : d1 pattern = 1) : d1296 pattern ≤ (0 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11001 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11003 (pattern : Twelve) (guard : d1 pattern = 1) : d1306 pattern ≤ (0 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11000 pattern childGuard
    simpa only [d1306, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11002 pattern childGuard
    simpa only [d1306, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11004 (pattern : Twelve) (guard : d1 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10993 pattern childGuard
    simpa only [d1313, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11003 pattern childGuard
    simpa only [d1313, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11005 (pattern : Twelve) (guard : d1836 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1314 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10983 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11004 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11006 (pattern : Twelve) (guard : d0 pattern = 1) : d1319 pattern ≤ (0 : Int) + d1314 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11007 (pattern : Twelve) (guard : d1890 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1314 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11005 pattern childGuard
    simpa only [d1890, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11006 pattern childGuard
    simpa only [d1890, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11008 (pattern : Twelve) (guard : d0 pattern = 1) : d1316 pattern ≤ (0 : Int) + d1317 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11009 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (0 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11010 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (0 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10963 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10884 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11011 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11009 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11010 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11012 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (0 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1283, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11011 pattern childGuard
    simpa only [d1283, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11013 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (0 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10909 pattern childGuard
    simpa only [d1283, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10886 pattern childGuard
    simpa only [d1283, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11014 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (0 : Int) + d1291 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11012 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11013 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11015 (pattern : Twelve) (guard : d1 pattern = 1) : d1301 pattern ≤ (0 : Int) + d1303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11014 pattern childGuard
    simpa only [d1301, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d1301, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11016 (pattern : Twelve) (guard : d1 pattern = 1) : d1309 pattern ≤ (0 : Int) + d1311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10990 pattern childGuard
    simpa only [d1309, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11015 pattern childGuard
    simpa only [d1309, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11017 (pattern : Twelve) (guard : d1 pattern = 1) : d1290 pattern ≤ (0 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10949 pattern childGuard
    simpa only [d1290, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10919 pattern childGuard
    simpa only [d1290, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11018 (pattern : Twelve) (guard : d1 pattern = 1) : d1302 pattern ≤ (0 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11017 pattern childGuard
    simpa only [d1302, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d1302, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11019 (pattern : Twelve) (guard : d1 pattern = 1) : d1310 pattern ≤ (0 : Int) + d1312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11000 pattern childGuard
    simpa only [d1310, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11018 pattern childGuard
    simpa only [d1310, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11020 (pattern : Twelve) (guard : d1 pattern = 1) : d1316 pattern ≤ (0 : Int) + d1317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11016 pattern childGuard
    simpa only [d1316, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11019 pattern childGuard
    simpa only [d1316, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11021 (pattern : Twelve) (guard : d1836 pattern = 1) : d1316 pattern ≤ (0 : Int) + d1317 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11008 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11020 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11022 (pattern : Twelve) (guard : d0 pattern = 1) : d1320 pattern ≤ (0 : Int) + d1317 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11023 (pattern : Twelve) (guard : d1890 pattern = 1) : d1322 pattern ≤ (0 : Int) + d1317 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11021 pattern childGuard
    simpa only [d1890, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11022 pattern childGuard
    simpa only [d1890, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11024 (pattern : Twelve) (guard : d1890 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1900 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1323, d1900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11007 pattern childGuard
    simpa only [d1323, d1900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1323, d1900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11023 pattern childGuard
    simpa only [d1323, d1900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11025 (pattern : Twelve) (guard : d0 pattern = 1) : d1660 pattern ≤ (0 : Int) + d1661 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11026 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10889 pattern childGuard
    simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10945 pattern childGuard
    simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11027 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (0 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c388 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11026 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11028 (pattern : Twelve) (guard : d1 pattern = 1) : d1649 pattern ≤ (0 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10991 pattern childGuard
    simpa only [d1649, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11027 pattern childGuard
    simpa only [d1649, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11029 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (0 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c392 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10948 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11030 (pattern : Twelve) (guard : d1 pattern = 1) : d1650 pattern ≤ (0 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11029 pattern childGuard
    simpa only [d1650, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d1650, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11031 (pattern : Twelve) (guard : d1 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11028 pattern childGuard
    simpa only [d1656, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11030 pattern childGuard
    simpa only [d1656, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11032 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10944 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11033 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (0 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10947 pattern childGuard
    simpa only [d20, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11032 pattern childGuard
    simpa only [d20, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11034 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (0 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11026 pattern childGuard
    simpa only [d1644, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11033 pattern childGuard
    simpa only [d1644, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11035 (pattern : Twelve) (guard : d1 pattern = 1) : d1645 pattern ≤ (0 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11026 pattern childGuard
    simpa only [d1645, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d1645, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11036 (pattern : Twelve) (guard : d1 pattern = 1) : d1647 pattern ≤ (0 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11034 pattern childGuard
    simpa only [d1647, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11035 pattern childGuard
    simpa only [d1647, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11037 (pattern : Twelve) (guard : d1 pattern = 1) : d1651 pattern ≤ (0 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11001 pattern childGuard
    simpa only [d1651, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11036 pattern childGuard
    simpa only [d1651, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11038 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10946 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11039 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11032 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11038 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11040 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (0 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10948 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11039 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11041 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (0 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11040 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10950 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11042 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (0 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11041 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11043 (pattern : Twelve) (guard : d1 pattern = 1) : d1657 pattern ≤ (0 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11037 pattern childGuard
    simpa only [d1657, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11042 pattern childGuard
    simpa only [d1657, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11044 (pattern : Twelve) (guard : d1 pattern = 1) : d1660 pattern ≤ (0 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11031 pattern childGuard
    simpa only [d1660, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11043 pattern childGuard
    simpa only [d1660, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11045 (pattern : Twelve) (guard : d1836 pattern = 1) : d1660 pattern ≤ (0 : Int) + d1661 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11025 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11044 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11046 (pattern : Twelve) (guard : d0 pattern = 1) : d1663 pattern ≤ (0 : Int) + d1661 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11047 (pattern : Twelve) (guard : d1890 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1661 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11045 pattern childGuard
    simpa only [d1890, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11046 pattern childGuard
    simpa only [d1890, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11048 (pattern : Twelve) (guard : d0 pattern = 1) : d26 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11049 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d0 pattern := by
  omega
theorem c11050 (pattern : Twelve) (guard : d0 pattern = 1) : d161 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11051 (pattern : Twelve) (guard : d1848 pattern = 1) : d171 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11050 pattern childGuard
    simpa only [d1848, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11052 (pattern : Twelve) (guard : d1901 pattern = 1) : d184 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11048 pattern childGuard
    simpa only [d1901, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11051 pattern childGuard
    simpa only [d1901, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11053 (pattern : Twelve) (guard : d0 pattern = 1) : d171 pattern ≤ (1 : Int) + d27 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11054 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d17 pattern := by
  omega
theorem c11055 (pattern : Twelve) (guard : d0 pattern = 1) : d163 pattern ≤ (1 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11056 (pattern : Twelve) (guard : d1848 pattern = 1) : d366 pattern ≤ (1 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d366, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1848, d366, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d366, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11055 pattern childGuard
    simpa only [d1848, d366, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11057 (pattern : Twelve) (guard : d1901 pattern = 1) : d372 pattern ≤ (1 : Int) + d27 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11053 pattern childGuard
    simpa only [d1901, d372, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11056 pattern childGuard
    simpa only [d1901, d372, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11058 (pattern : Twelve) (guard : d1901 pattern = 1) : d389 pattern ≤ (1 : Int) + d1902 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d389, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11052 pattern childGuard
    simpa only [d389, d1902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d389, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11057 pattern childGuard
    simpa only [d389, d1902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11059 (pattern : Twelve) (guard : d0 pattern = 1) : d171 pattern ≤ (1 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban21.Diagram
