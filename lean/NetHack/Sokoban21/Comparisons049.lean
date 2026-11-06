/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons048
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c6860 (pattern : Twelve) (guard : d1855 pattern = 1) : d1083 pattern ≤ (0 : Int) + d960 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1083, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6856 pattern childGuard
    simpa only [d1855, d1083, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1083, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6859 pattern childGuard
    simpa only [d1855, d1083, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6861 (pattern : Twelve) (guard : d1855 pattern = 1) : d1090 pattern ≤ (0 : Int) + d965 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1090, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6855 pattern childGuard
    simpa only [d1090, d965, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1090, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6860 pattern childGuard
    simpa only [d1090, d965, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6862 (pattern : Twelve) (guard : d1855 pattern = 1) : d1091 pattern ≤ (0 : Int) + d966 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1091, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6849 pattern childGuard
    simpa only [d1091, d966, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1091, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1603 pattern childGuard
    simpa only [d1091, d966, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6863 (pattern : Twelve) (guard : d1855 pattern = 1) : d1096 pattern ≤ (0 : Int) + d971 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1096, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6861 pattern childGuard
    simpa only [d1096, d971, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1096, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6862 pattern childGuard
    simpa only [d1096, d971, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6864 (pattern : Twelve) (guard : d1855 pattern = 1) : d1099 pattern ≤ (0 : Int) + d973 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1099, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6851 pattern childGuard
    simpa only [d1099, d973, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1099, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6863 pattern childGuard
    simpa only [d1099, d973, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6865 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d943 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6866 (pattern : Twelve) (guard : d1853 pattern = 1) : d438 pattern ≤ (0 : Int) + d953 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d438, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c158 pattern childGuard
    simpa only [d1853, d438, d953, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d438, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6865 pattern childGuard
    simpa only [d1853, d438, d953, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6867 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6868 (pattern : Twelve) (guard : d1848 pattern = 1) : d17 pattern ≤ (0 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6867 pattern childGuard
    simpa only [d1848, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6869 (pattern : Twelve) (guard : d1849 pattern = 1) : d17 pattern ≤ (0 : Int) + d946 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6868 pattern childGuard
    simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c259 pattern childGuard
    simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6870 (pattern : Twelve) (guard : d1854 pattern = 1) : d1073 pattern ≤ (0 : Int) + d954 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1073, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6869 pattern childGuard
    simpa only [d1854, d1073, d954, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1073, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6840 pattern childGuard
    simpa only [d1854, d1073, d954, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6871 (pattern : Twelve) (guard : d1855 pattern = 1) : d1084 pattern ≤ (0 : Int) + d961 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1084, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6866 pattern childGuard
    simpa only [d1855, d1084, d961, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1084, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6870 pattern childGuard
    simpa only [d1855, d1084, d961, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6872 (pattern : Twelve) (guard : d1855 pattern = 1) : d1092 pattern ≤ (0 : Int) + d967 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1092, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6871 pattern childGuard
    simpa only [d1092, d967, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1092, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6849 pattern childGuard
    simpa only [d1092, d967, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6873 (pattern : Twelve) (guard : d1853 pattern = 1) : d441 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d441, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c163 pattern childGuard
    simpa only [d1853, d441, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d441, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6753 pattern childGuard
    simpa only [d1853, d441, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6874 (pattern : Twelve) (guard : d1855 pattern = 1) : d1085 pattern ≤ (0 : Int) + d958 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1085, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6873 pattern childGuard
    simpa only [d1855, d1085, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1085, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6854 pattern childGuard
    simpa only [d1855, d1085, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6875 (pattern : Twelve) (guard : d1855 pattern = 1) : d1093 pattern ≤ (0 : Int) + d968 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1093, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6874 pattern childGuard
    simpa only [d1093, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1093, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6860 pattern childGuard
    simpa only [d1093, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6876 (pattern : Twelve) (guard : d1855 pattern = 1) : d1097 pattern ≤ (0 : Int) + d972 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1097, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6875 pattern childGuard
    simpa only [d1097, d972, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1097, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6862 pattern childGuard
    simpa only [d1097, d972, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6877 (pattern : Twelve) (guard : d1855 pattern = 1) : d1100 pattern ≤ (0 : Int) + d974 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1100, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6872 pattern childGuard
    simpa only [d1100, d974, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1100, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6876 pattern childGuard
    simpa only [d1100, d974, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6878 (pattern : Twelve) (guard : d1855 pattern = 1) : d1102 pattern ≤ (0 : Int) + d976 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1102, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6864 pattern childGuard
    simpa only [d1102, d976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1102, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6877 pattern childGuard
    simpa only [d1102, d976, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6879 (pattern : Twelve) (guard : d1855 pattern = 1) : d1084 pattern ≤ (0 : Int) + d962 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1084, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6866 pattern childGuard
    simpa only [d1855, d1084, d962, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1084, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6846 pattern childGuard
    simpa only [d1855, d1084, d962, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6880 (pattern : Twelve) (guard : d1855 pattern = 1) : d1092 pattern ≤ (0 : Int) + d969 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1092, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6879 pattern childGuard
    simpa only [d1092, d969, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1092, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6849 pattern childGuard
    simpa only [d1092, d969, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6881 (pattern : Twelve) (guard : d1855 pattern = 1) : d1100 pattern ≤ (0 : Int) + d975 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1100, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6880 pattern childGuard
    simpa only [d1100, d975, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1100, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6876 pattern childGuard
    simpa only [d1100, d975, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6882 (pattern : Twelve) (guard : d1855 pattern = 1) : d1100 pattern ≤ (0 : Int) + d977 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6881 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6877 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6883 (pattern : Twelve) (guard : d1855 pattern = 1) : d1103 pattern ≤ (0 : Int) + d978 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1103, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6878 pattern childGuard
    simpa only [d1103, d978, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1103, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6882 pattern childGuard
    simpa only [d1103, d978, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6884 (pattern : Twelve) (guard : d0 pattern = 1) : d879 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6885 (pattern : Twelve) (guard : d1849 pattern = 1) : d886 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d886, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1676 pattern childGuard
    simpa only [d1849, d886, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d886, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6884 pattern childGuard
    simpa only [d1849, d886, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6886 (pattern : Twelve) (guard : d1854 pattern = 1) : d1076 pattern ≤ (0 : Int) + d949 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1076, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6885 pattern childGuard
    simpa only [d1854, d1076, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1076, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6840 pattern childGuard
    simpa only [d1854, d1076, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6887 (pattern : Twelve) (guard : d1855 pattern = 1) : d1086 pattern ≤ (0 : Int) + d958 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1086, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6873 pattern childGuard
    simpa only [d1855, d1086, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1086, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6886 pattern childGuard
    simpa only [d1855, d1086, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6888 (pattern : Twelve) (guard : d0 pattern = 1) : d118 pattern ≤ (0 : Int) + d24 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6889 (pattern : Twelve) (guard : d1848 pattern = 1) : d881 pattern ≤ (0 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d881, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1340 pattern childGuard
    simpa only [d1848, d881, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d881, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6888 pattern childGuard
    simpa only [d1848, d881, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6890 (pattern : Twelve) (guard : d1849 pattern = 1) : d888 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d888, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6889 pattern childGuard
    simpa only [d1849, d888, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d888, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c353 pattern childGuard
    simpa only [d1849, d888, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6891 (pattern : Twelve) (guard : d1854 pattern = 1) : d1077 pattern ≤ (0 : Int) + d952 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1077, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6890 pattern childGuard
    simpa only [d1854, d1077, d952, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1077, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6858 pattern childGuard
    simpa only [d1854, d1077, d952, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6892 (pattern : Twelve) (guard : d1855 pattern = 1) : d1087 pattern ≤ (0 : Int) + d960 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1087, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6856 pattern childGuard
    simpa only [d1855, d1087, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1087, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6891 pattern childGuard
    simpa only [d1855, d1087, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6893 (pattern : Twelve) (guard : d1855 pattern = 1) : d1094 pattern ≤ (0 : Int) + d968 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1094, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6887 pattern childGuard
    simpa only [d1094, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1094, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6892 pattern childGuard
    simpa only [d1094, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6894 (pattern : Twelve) (guard : d1855 pattern = 1) : d1098 pattern ≤ (0 : Int) + d972 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1098, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6893 pattern childGuard
    simpa only [d1098, d972, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1098, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6862 pattern childGuard
    simpa only [d1098, d972, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6895 (pattern : Twelve) (guard : d1855 pattern = 1) : d1101 pattern ≤ (0 : Int) + d975 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1101, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6880 pattern childGuard
    simpa only [d1101, d975, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1101, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6894 pattern childGuard
    simpa only [d1101, d975, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6896 (pattern : Twelve) (guard : d1855 pattern = 1) : d1101 pattern ≤ (0 : Int) + d974 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1101, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6872 pattern childGuard
    simpa only [d1101, d974, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1101, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6894 pattern childGuard
    simpa only [d1101, d974, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6897 (pattern : Twelve) (guard : d1855 pattern = 1) : d1101 pattern ≤ (0 : Int) + d977 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6895 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6896 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6898 (pattern : Twelve) (guard : d1855 pattern = 1) : d1104 pattern ≤ (0 : Int) + d979 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1104, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6883 pattern childGuard
    simpa only [d1104, d979, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1104, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6897 pattern childGuard
    simpa only [d1104, d979, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6899 (pattern : Twelve) (guard : d0 pattern = 1) : d908 pattern ≤ (0 : Int) + d1380 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6900 (pattern : Twelve) (guard : d1853 pattern = 1) : d1070 pattern ≤ (0 : Int) + d1385 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1070, d1385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c242 pattern childGuard
    simpa only [d1853, d1070, d1385, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1070, d1385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6899 pattern childGuard
    simpa only [d1853, d1070, d1385, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6901 (pattern : Twelve) (guard : d1854 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1386 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1294, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4523 pattern childGuard
    simpa only [d1854, d1294, d1386, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1294, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1294, d1386, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6902 (pattern : Twelve) (guard : d1855 pattern = 1) : d1472 pattern ≤ (0 : Int) + d1393 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1472, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6900 pattern childGuard
    simpa only [d1855, d1472, d1393, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1472, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6901 pattern childGuard
    simpa only [d1855, d1472, d1393, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6903 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1382 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6904 (pattern : Twelve) (guard : d1853 pattern = 1) : d1072 pattern ≤ (0 : Int) + d1387 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1072, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c252 pattern childGuard
    simpa only [d1853, d1072, d1387, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1072, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6903 pattern childGuard
    simpa only [d1853, d1072, d1387, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6905 (pattern : Twelve) (guard : d1849 pattern = 1) : d1286 pattern ≤ (0 : Int) + d942 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1286, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1747 pattern childGuard
    simpa only [d1849, d1286, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1286, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c101 pattern childGuard
    simpa only [d1849, d1286, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6906 (pattern : Twelve) (guard : d1854 pattern = 1) : d1296 pattern ≤ (0 : Int) + d1388 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1296, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6905 pattern childGuard
    simpa only [d1854, d1296, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1296, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1296, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6907 (pattern : Twelve) (guard : d1855 pattern = 1) : d1473 pattern ≤ (0 : Int) + d1394 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1473, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6904 pattern childGuard
    simpa only [d1855, d1473, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1473, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6906 pattern childGuard
    simpa only [d1855, d1473, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6908 (pattern : Twelve) (guard : d1855 pattern = 1) : d1479 pattern ≤ (0 : Int) + d1398 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1479, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6902 pattern childGuard
    simpa only [d1479, d1398, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1479, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6907 pattern childGuard
    simpa only [d1479, d1398, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6909 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1380 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6910 (pattern : Twelve) (guard : d1853 pattern = 1) : d1073 pattern ≤ (0 : Int) + d1389 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1073, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c260 pattern childGuard
    simpa only [d1853, d1073, d1389, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1073, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6909 pattern childGuard
    simpa only [d1853, d1073, d1389, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6911 (pattern : Twelve) (guard : d1855 pattern = 1) : d1474 pattern ≤ (0 : Int) + d1395 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1474, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6910 pattern childGuard
    simpa only [d1855, d1474, d1395, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1474, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6901 pattern childGuard
    simpa only [d1855, d1474, d1395, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6912 (pattern : Twelve) (guard : d1855 pattern = 1) : d1480 pattern ≤ (0 : Int) + d1399 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1480, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6911 pattern childGuard
    simpa only [d1480, d1399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1480, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6907 pattern childGuard
    simpa only [d1480, d1399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6913 (pattern : Twelve) (guard : d1855 pattern = 1) : d1484 pattern ≤ (0 : Int) + d1403 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1484, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6908 pattern childGuard
    simpa only [d1484, d1403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1484, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6912 pattern childGuard
    simpa only [d1484, d1403, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6914 (pattern : Twelve) (guard : d1853 pattern = 1) : d1074 pattern ≤ (0 : Int) + d1387 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1074, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c271 pattern childGuard
    simpa only [d1853, d1074, d1387, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1074, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6903 pattern childGuard
    simpa only [d1853, d1074, d1387, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6915 (pattern : Twelve) (guard : d1849 pattern = 1) : d817 pattern ≤ (0 : Int) + d942 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1747 pattern childGuard
    simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c348 pattern childGuard
    simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6916 (pattern : Twelve) (guard : d1854 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1388 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1298, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6915 pattern childGuard
    simpa only [d1854, d1298, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1298, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1298, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6917 (pattern : Twelve) (guard : d1855 pattern = 1) : d1475 pattern ≤ (0 : Int) + d1394 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1475, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6914 pattern childGuard
    simpa only [d1855, d1475, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1475, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6916 pattern childGuard
    simpa only [d1855, d1475, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6918 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1383 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6919 (pattern : Twelve) (guard : d1853 pattern = 1) : d1075 pattern ≤ (0 : Int) + d1390 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1075, d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c277 pattern childGuard
    simpa only [d1853, d1075, d1390, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1075, d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6918 pattern childGuard
    simpa only [d1853, d1075, d1390, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6920 (pattern : Twelve) (guard : d1849 pattern = 1) : d1289 pattern ≤ (0 : Int) + d945 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1289, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1763 pattern childGuard
    simpa only [d1849, d1289, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1289, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c144 pattern childGuard
    simpa only [d1849, d1289, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6921 (pattern : Twelve) (guard : d1854 pattern = 1) : d1300 pattern ≤ (0 : Int) + d1391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1300, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6920 pattern childGuard
    simpa only [d1854, d1300, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1300, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1300, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6922 (pattern : Twelve) (guard : d1855 pattern = 1) : d1476 pattern ≤ (0 : Int) + d1396 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1476, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6919 pattern childGuard
    simpa only [d1855, d1476, d1396, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1476, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6921 pattern childGuard
    simpa only [d1855, d1476, d1396, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6923 (pattern : Twelve) (guard : d1855 pattern = 1) : d1481 pattern ≤ (0 : Int) + d1400 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1481, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6917 pattern childGuard
    simpa only [d1481, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1481, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6922 pattern childGuard
    simpa only [d1481, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6924 (pattern : Twelve) (guard : d1855 pattern = 1) : d1482 pattern ≤ (0 : Int) + d1401 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1482, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6907 pattern childGuard
    simpa only [d1482, d1401, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1482, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1603 pattern childGuard
    simpa only [d1482, d1401, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6925 (pattern : Twelve) (guard : d1855 pattern = 1) : d1485 pattern ≤ (0 : Int) + d1404 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1485, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6923 pattern childGuard
    simpa only [d1485, d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1485, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6924 pattern childGuard
    simpa only [d1485, d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6926 (pattern : Twelve) (guard : d1855 pattern = 1) : d1487 pattern ≤ (0 : Int) + d1405 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1487, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6913 pattern childGuard
    simpa only [d1487, d1405, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1487, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6925 pattern childGuard
    simpa only [d1487, d1405, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6927 (pattern : Twelve) (guard : d0 pattern = 1) : d19 pattern ≤ (0 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6928 (pattern : Twelve) (guard : d1848 pattern = 1) : d19 pattern ≤ (0 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6927 pattern childGuard
    simpa only [d1848, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6929 (pattern : Twelve) (guard : d1849 pattern = 1) : d19 pattern ≤ (0 : Int) + d1384 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6928 pattern childGuard
    simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c329 pattern childGuard
    simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6930 (pattern : Twelve) (guard : d1854 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1392 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1294, d1392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6929 pattern childGuard
    simpa only [d1854, d1294, d1392, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1294, d1392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1294, d1392, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6931 (pattern : Twelve) (guard : d1855 pattern = 1) : d1474 pattern ≤ (0 : Int) + d1397 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1474, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6910 pattern childGuard
    simpa only [d1855, d1474, d1397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1474, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6930 pattern childGuard
    simpa only [d1855, d1474, d1397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6932 (pattern : Twelve) (guard : d1855 pattern = 1) : d1480 pattern ≤ (0 : Int) + d1402 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1480, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6931 pattern childGuard
    simpa only [d1480, d1402, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1480, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6907 pattern childGuard
    simpa only [d1480, d1402, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6933 (pattern : Twelve) (guard : d1855 pattern = 1) : d1488 pattern ≤ (0 : Int) + d1406 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1488, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6932 pattern childGuard
    simpa only [d1488, d1406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1488, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6925 pattern childGuard
    simpa only [d1488, d1406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6934 (pattern : Twelve) (guard : d1855 pattern = 1) : d1490 pattern ≤ (0 : Int) + d1408 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1490, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6926 pattern childGuard
    simpa only [d1490, d1408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1490, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6933 pattern childGuard
    simpa only [d1490, d1408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6935 (pattern : Twelve) (guard : d1855 pattern = 1) : d1488 pattern ≤ (0 : Int) + d1407 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1488, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6912 pattern childGuard
    simpa only [d1488, d1407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1488, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6925 pattern childGuard
    simpa only [d1488, d1407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6936 (pattern : Twelve) (guard : d1855 pattern = 1) : d1488 pattern ≤ (0 : Int) + d1409 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6935 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6933 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6937 (pattern : Twelve) (guard : d1855 pattern = 1) : d1491 pattern ≤ (0 : Int) + d1410 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1491, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6934 pattern childGuard
    simpa only [d1491, d1410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1491, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6936 pattern childGuard
    simpa only [d1491, d1410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6938 (pattern : Twelve) (guard : d0 pattern = 1) : d1329 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6939 (pattern : Twelve) (guard : d1849 pattern = 1) : d1336 pattern ≤ (0 : Int) + d942 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1336, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1747 pattern childGuard
    simpa only [d1849, d1336, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1336, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6938 pattern childGuard
    simpa only [d1849, d1336, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6940 (pattern : Twelve) (guard : d1854 pattern = 1) : d1342 pattern ≤ (0 : Int) + d1388 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1342, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6939 pattern childGuard
    simpa only [d1854, d1342, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1342, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1342, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6941 (pattern : Twelve) (guard : d1855 pattern = 1) : d1477 pattern ≤ (0 : Int) + d1394 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1477, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6914 pattern childGuard
    simpa only [d1855, d1477, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1477, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6940 pattern childGuard
    simpa only [d1855, d1477, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6942 (pattern : Twelve) (guard : d0 pattern = 1) : d22 pattern ≤ (0 : Int) + d21 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6943 (pattern : Twelve) (guard : d1848 pattern = 1) : d1332 pattern ≤ (0 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1332, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c392 pattern childGuard
    simpa only [d1848, d1332, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1332, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6942 pattern childGuard
    simpa only [d1848, d1332, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6944 (pattern : Twelve) (guard : d1849 pattern = 1) : d1338 pattern ≤ (0 : Int) + d945 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1338, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6943 pattern childGuard
    simpa only [d1849, d1338, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1338, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c411 pattern childGuard
    simpa only [d1849, d1338, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6945 (pattern : Twelve) (guard : d1854 pattern = 1) : d1344 pattern ≤ (0 : Int) + d1391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1344, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6944 pattern childGuard
    simpa only [d1854, d1344, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1344, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1344, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6946 (pattern : Twelve) (guard : d1855 pattern = 1) : d1478 pattern ≤ (0 : Int) + d1396 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1478, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6919 pattern childGuard
    simpa only [d1855, d1478, d1396, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1478, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6945 pattern childGuard
    simpa only [d1855, d1478, d1396, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6947 (pattern : Twelve) (guard : d1855 pattern = 1) : d1483 pattern ≤ (0 : Int) + d1400 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1483, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6941 pattern childGuard
    simpa only [d1483, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1483, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6946 pattern childGuard
    simpa only [d1483, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6948 (pattern : Twelve) (guard : d1855 pattern = 1) : d1486 pattern ≤ (0 : Int) + d1404 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1486, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6947 pattern childGuard
    simpa only [d1486, d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1486, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6924 pattern childGuard
    simpa only [d1486, d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6949 (pattern : Twelve) (guard : d1855 pattern = 1) : d1489 pattern ≤ (0 : Int) + d1407 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1489, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6912 pattern childGuard
    simpa only [d1489, d1407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1489, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6948 pattern childGuard
    simpa only [d1489, d1407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6950 (pattern : Twelve) (guard : d1855 pattern = 1) : d1489 pattern ≤ (0 : Int) + d1406 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1489, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6932 pattern childGuard
    simpa only [d1489, d1406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1489, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6948 pattern childGuard
    simpa only [d1489, d1406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6951 (pattern : Twelve) (guard : d1855 pattern = 1) : d1489 pattern ≤ (0 : Int) + d1409 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6949 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6950 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6952 (pattern : Twelve) (guard : d1855 pattern = 1) : d1492 pattern ≤ (0 : Int) + d1411 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1492, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6937 pattern childGuard
    simpa only [d1492, d1411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1492, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6951 pattern childGuard
    simpa only [d1492, d1411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6953 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1689 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6954 (pattern : Twelve) (guard : d1853 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1693 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1294, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c330 pattern childGuard
    simpa only [d1853, d1294, d1693, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1294, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6953 pattern childGuard
    simpa only [d1853, d1294, d1693, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6955 (pattern : Twelve) (guard : d1854 pattern = 1) : d1650 pattern ≤ (0 : Int) + d1694 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1650, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4567 pattern childGuard
    simpa only [d1854, d1650, d1694, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1650, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1650, d1694, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6956 (pattern : Twelve) (guard : d1855 pattern = 1) : d1730 pattern ≤ (0 : Int) + d1697 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1730, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6954 pattern childGuard
    simpa only [d1855, d1730, d1697, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1730, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6955 pattern childGuard
    simpa only [d1855, d1730, d1697, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6957 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1691 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6958 (pattern : Twelve) (guard : d1853 pattern = 1) : d1296 pattern ≤ (0 : Int) + d1695 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1296, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c337 pattern childGuard
    simpa only [d1853, d1296, d1695, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1296, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6957 pattern childGuard
    simpa only [d1853, d1296, d1695, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6959 (pattern : Twelve) (guard : d1855 pattern = 1) : d1731 pattern ≤ (0 : Int) + d1698 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1731, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6958 pattern childGuard
    simpa only [d1855, d1731, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1731, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6921 pattern childGuard
    simpa only [d1855, d1731, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6960 (pattern : Twelve) (guard : d1855 pattern = 1) : d1736 pattern ≤ (0 : Int) + d1700 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1736, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6956 pattern childGuard
    simpa only [d1736, d1700, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1736, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6959 pattern childGuard
    simpa only [d1736, d1700, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6961 (pattern : Twelve) (guard : d1853 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1695 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1298, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c349 pattern childGuard
    simpa only [d1853, d1298, d1695, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1298, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6957 pattern childGuard
    simpa only [d1853, d1298, d1695, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6962 (pattern : Twelve) (guard : d1849 pattern = 1) : d821 pattern ≤ (0 : Int) + d945 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1763 pattern childGuard
    simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c406 pattern childGuard
    simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6963 (pattern : Twelve) (guard : d1854 pattern = 1) : d1653 pattern ≤ (0 : Int) + d1391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1653, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6962 pattern childGuard
    simpa only [d1854, d1653, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1653, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1653, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6964 (pattern : Twelve) (guard : d1855 pattern = 1) : d1732 pattern ≤ (0 : Int) + d1698 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1732, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6961 pattern childGuard
    simpa only [d1855, d1732, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1732, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6963 pattern childGuard
    simpa only [d1855, d1732, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6965 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1692 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6966 (pattern : Twelve) (guard : d1853 pattern = 1) : d1300 pattern ≤ (0 : Int) + d1696 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1300, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d1853, d1300, d1696, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1300, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6965 pattern childGuard
    simpa only [d1853, d1300, d1696, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6967 (pattern : Twelve) (guard : d1854 pattern = 1) : d1655 pattern ≤ (0 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5228 pattern childGuard
    simpa only [d1854, d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6968 (pattern : Twelve) (guard : d1855 pattern = 1) : d1733 pattern ≤ (0 : Int) + d1699 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1733, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6966 pattern childGuard
    simpa only [d1855, d1733, d1699, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1733, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6967 pattern childGuard
    simpa only [d1855, d1733, d1699, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6969 (pattern : Twelve) (guard : d1855 pattern = 1) : d1737 pattern ≤ (0 : Int) + d1701 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1737, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6964 pattern childGuard
    simpa only [d1737, d1701, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1737, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6968 pattern childGuard
    simpa only [d1737, d1701, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6970 (pattern : Twelve) (guard : d1855 pattern = 1) : d1738 pattern ≤ (0 : Int) + d1702 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1738, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6959 pattern childGuard
    simpa only [d1738, d1702, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1738, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1603 pattern childGuard
    simpa only [d1738, d1702, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6971 (pattern : Twelve) (guard : d1855 pattern = 1) : d1740 pattern ≤ (0 : Int) + d1703 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1740, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6969 pattern childGuard
    simpa only [d1740, d1703, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1740, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6970 pattern childGuard
    simpa only [d1740, d1703, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6972 (pattern : Twelve) (guard : d1855 pattern = 1) : d1742 pattern ≤ (0 : Int) + d1704 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1742, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6960 pattern childGuard
    simpa only [d1742, d1704, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1742, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6971 pattern childGuard
    simpa only [d1742, d1704, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6973 (pattern : Twelve) (guard : d1855 pattern = 1) : d1734 pattern ≤ (0 : Int) + d1698 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1734, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6961 pattern childGuard
    simpa only [d1855, d1734, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1734, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6921 pattern childGuard
    simpa only [d1855, d1734, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6974 (pattern : Twelve) (guard : d1855 pattern = 1) : d1735 pattern ≤ (0 : Int) + d1699 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1735, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6966 pattern childGuard
    simpa only [d1855, d1735, d1699, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1735, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1820 pattern childGuard
    simpa only [d1855, d1735, d1699, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6975 (pattern : Twelve) (guard : d1855 pattern = 1) : d1739 pattern ≤ (0 : Int) + d1701 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1739, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6973 pattern childGuard
    simpa only [d1739, d1701, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1739, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6974 pattern childGuard
    simpa only [d1739, d1701, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6976 (pattern : Twelve) (guard : d1855 pattern = 1) : d1741 pattern ≤ (0 : Int) + d1703 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1741, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6975 pattern childGuard
    simpa only [d1741, d1703, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1741, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6970 pattern childGuard
    simpa only [d1741, d1703, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6977 (pattern : Twelve) (guard : d1855 pattern = 1) : d1743 pattern ≤ (0 : Int) + d1704 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1743, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6960 pattern childGuard
    simpa only [d1743, d1704, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1743, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6976 pattern childGuard
    simpa only [d1743, d1704, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6978 (pattern : Twelve) (guard : d1855 pattern = 1) : d1744 pattern ≤ (0 : Int) + d1704 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6972 pattern childGuard
    simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6977 pattern childGuard
    simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6979 (pattern : Twelve) (guard : d1865 pattern = 1) : d477 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4957 pattern childGuard
    simpa only [d1865, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6980 (pattern : Twelve) (guard : d1865 pattern = 1) : d498 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2824 pattern childGuard
    simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6979 pattern childGuard
    simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6981 (pattern : Twelve) (guard : d0 pattern = 1) : d157 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6982 (pattern : Twelve) (guard : d1865 pattern = 1) : d478 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d478, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6981 pattern childGuard
    simpa only [d1865, d478, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6983 (pattern : Twelve) (guard : d1865 pattern = 1) : d499 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2824 pattern childGuard
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6982 pattern childGuard
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6984 (pattern : Twelve) (guard : d1865 pattern = 1) : d532 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6980 pattern childGuard
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6983 pattern childGuard
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6985 (pattern : Twelve) (guard : d0 pattern = 1) : d157 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6986 (pattern : Twelve) (guard : d1865 pattern = 1) : d161 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d1865, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6985 pattern childGuard
    simpa only [d1865, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6987 (pattern : Twelve) (guard : d1865 pattern = 1) : d171 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2824 pattern childGuard
    simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6986 pattern childGuard
    simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6988 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6989 (pattern : Twelve) (guard : d1865 pattern = 1) : d162 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d162, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d162, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d162, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6988 pattern childGuard
    simpa only [d1865, d162, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6990 (pattern : Twelve) (guard : d1865 pattern = 1) : d479 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d1865, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d1865, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6991 (pattern : Twelve) (guard : d1865 pattern = 1) : d500 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d500, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6989 pattern childGuard
    simpa only [d500, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d500, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6990 pattern childGuard
    simpa only [d500, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6992 (pattern : Twelve) (guard : d1865 pattern = 1) : d533 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d533, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6987 pattern childGuard
    simpa only [d533, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d533, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6991 pattern childGuard
    simpa only [d533, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6993 (pattern : Twelve) (guard : d1865 pattern = 1) : d561 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d561, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6984 pattern childGuard
    simpa only [d561, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d561, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6992 pattern childGuard
    simpa only [d561, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6994 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6995 (pattern : Twelve) (guard : d1865 pattern = 1) : d162 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6994 pattern childGuard
    simpa only [d1865, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6996 (pattern : Twelve) (guard : d1865 pattern = 1) : d480 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c881 pattern childGuard
    simpa only [d1865, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6997 (pattern : Twelve) (guard : d1865 pattern = 1) : d501 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6995 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6996 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6998 (pattern : Twelve) (guard : d1865 pattern = 1) : d534 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6983 pattern childGuard
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6997 pattern childGuard
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6999 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban21.Diagram
