/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons063
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c8960 (pattern : Twelve) (guard : d1848 pattern = 1) : d133 pattern ≤ (0 : Int) + d386 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d133, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8959 pattern childGuard
    simpa only [d133, d386, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d133, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5401 pattern childGuard
    simpa only [d133, d386, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8961 (pattern : Twelve) (guard : d1848 pattern = 1) : d142 pattern ≤ (0 : Int) + d400 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d142, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d142, d400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d142, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8960 pattern childGuard
    simpa only [d142, d400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8962 (pattern : Twelve) (guard : d1848 pattern = 1) : d127 pattern ≤ (0 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d127, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1340 pattern childGuard
    simpa only [d1848, d127, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d127, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1537 pattern childGuard
    simpa only [d1848, d127, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8963 (pattern : Twelve) (guard : d1848 pattern = 1) : d135 pattern ≤ (0 : Int) + d388 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d135, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8962 pattern childGuard
    simpa only [d135, d388, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d135, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5446 pattern childGuard
    simpa only [d135, d388, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8964 (pattern : Twelve) (guard : d1848 pattern = 1) : d143 pattern ≤ (0 : Int) + d401 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d143, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6606 pattern childGuard
    simpa only [d143, d401, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d143, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8963 pattern childGuard
    simpa only [d143, d401, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8965 (pattern : Twelve) (guard : d1848 pattern = 1) : d148 pattern ≤ (0 : Int) + d408 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d148, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8961 pattern childGuard
    simpa only [d148, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d148, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8964 pattern childGuard
    simpa only [d148, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8966 (pattern : Twelve) (guard : d1848 pattern = 1) : d151 pattern ≤ (0 : Int) + d414 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d151, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8958 pattern childGuard
    simpa only [d151, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d151, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8965 pattern childGuard
    simpa only [d151, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8967 (pattern : Twelve) (guard : d1848 pattern = 1) : d152 pattern ≤ (0 : Int) + d412 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d152, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8951 pattern childGuard
    simpa only [d152, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d152, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d152, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8968 (pattern : Twelve) (guard : d1848 pattern = 1) : d154 pattern ≤ (0 : Int) + d418 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d154, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8966 pattern childGuard
    simpa only [d154, d418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d154, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8967 pattern childGuard
    simpa only [d154, d418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8969 (pattern : Twelve) (guard : d1848 pattern = 1) : d155 pattern ≤ (0 : Int) + d421 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d155, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8953 pattern childGuard
    simpa only [d155, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d155, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8968 pattern childGuard
    simpa only [d155, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8970 (pattern : Twelve) (guard : d1848 pattern = 1) : d156 pattern ≤ (0 : Int) + d424 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d156, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8939 pattern childGuard
    simpa only [d156, d424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d156, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8969 pattern childGuard
    simpa only [d156, d424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8971 (pattern : Twelve) (guard : d1848 pattern = 1) : d826 pattern ≤ (0 : Int) + d1033 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d826, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d826, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d826, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5577 pattern childGuard
    simpa only [d826, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8972 (pattern : Twelve) (guard : d1848 pattern = 1) : d840 pattern ≤ (0 : Int) + d1040 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d840, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2670 pattern childGuard
    simpa only [d840, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d840, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8971 pattern childGuard
    simpa only [d840, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8973 (pattern : Twelve) (guard : d1848 pattern = 1) : d841 pattern ≤ (0 : Int) + d1041 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d841, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2753 pattern childGuard
    simpa only [d841, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d841, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4219 pattern childGuard
    simpa only [d841, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8974 (pattern : Twelve) (guard : d1848 pattern = 1) : d854 pattern ≤ (0 : Int) + d1049 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d854, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8972 pattern childGuard
    simpa only [d854, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d854, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8973 pattern childGuard
    simpa only [d854, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8975 (pattern : Twelve) (guard : d1848 pattern = 1) : d861 pattern ≤ (0 : Int) + d1054 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d861, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4221 pattern childGuard
    simpa only [d861, d1054, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d861, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8974 pattern childGuard
    simpa only [d861, d1054, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8976 (pattern : Twelve) (guard : d1848 pattern = 1) : d840 pattern ≤ (0 : Int) + d1042 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d840, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2589 pattern childGuard
    simpa only [d840, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d840, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8971 pattern childGuard
    simpa only [d840, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8977 (pattern : Twelve) (guard : d1848 pattern = 1) : d854 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d854, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8976 pattern childGuard
    simpa only [d854, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d854, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8973 pattern childGuard
    simpa only [d854, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8978 (pattern : Twelve) (guard : d1848 pattern = 1) : d861 pattern ≤ (0 : Int) + d1055 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d861, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4227 pattern childGuard
    simpa only [d861, d1055, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d861, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8977 pattern childGuard
    simpa only [d861, d1055, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8979 (pattern : Twelve) (guard : d1848 pattern = 1) : d861 pattern ≤ (0 : Int) + d1060 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8975 pattern childGuard
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8978 pattern childGuard
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8980 (pattern : Twelve) (guard : d1848 pattern = 1) : d819 pattern ≤ (0 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d819, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d1848, d819, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d819, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2923 pattern childGuard
    simpa only [d1848, d819, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8981 (pattern : Twelve) (guard : d1848 pattern = 1) : d828 pattern ≤ (0 : Int) + d1033 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d828, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d828, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d828, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8980 pattern childGuard
    simpa only [d828, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8982 (pattern : Twelve) (guard : d1848 pattern = 1) : d842 pattern ≤ (0 : Int) + d1043 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d842, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2686 pattern childGuard
    simpa only [d842, d1043, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d842, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8981 pattern childGuard
    simpa only [d842, d1043, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8983 (pattern : Twelve) (guard : d1848 pattern = 1) : d843 pattern ≤ (0 : Int) + d1041 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d843, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d843, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d843, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4219 pattern childGuard
    simpa only [d843, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8984 (pattern : Twelve) (guard : d1848 pattern = 1) : d855 pattern ≤ (0 : Int) + d1051 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d855, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8982 pattern childGuard
    simpa only [d855, d1051, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d855, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8983 pattern childGuard
    simpa only [d855, d1051, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8985 (pattern : Twelve) (guard : d1848 pattern = 1) : d829 pattern ≤ (0 : Int) + d1034 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d829, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1342 pattern childGuard
    simpa only [d829, d1034, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d829, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5596 pattern childGuard
    simpa only [d829, d1034, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8986 (pattern : Twelve) (guard : d1848 pattern = 1) : d844 pattern ≤ (0 : Int) + d1044 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d844, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d844, d1044, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d844, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8985 pattern childGuard
    simpa only [d844, d1044, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8987 (pattern : Twelve) (guard : d1848 pattern = 1) : d831 pattern ≤ (0 : Int) + d1035 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d831, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1432 pattern childGuard
    simpa only [d831, d1035, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d831, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1541 pattern childGuard
    simpa only [d831, d1035, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8988 (pattern : Twelve) (guard : d1848 pattern = 1) : d845 pattern ≤ (0 : Int) + d1045 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d845, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2769 pattern childGuard
    simpa only [d845, d1045, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d845, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8987 pattern childGuard
    simpa only [d845, d1045, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8989 (pattern : Twelve) (guard : d1848 pattern = 1) : d856 pattern ≤ (0 : Int) + d1052 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d856, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8986 pattern childGuard
    simpa only [d856, d1052, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d856, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8988 pattern childGuard
    simpa only [d856, d1052, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8990 (pattern : Twelve) (guard : d1848 pattern = 1) : d862 pattern ≤ (0 : Int) + d1056 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d862, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8984 pattern childGuard
    simpa only [d862, d1056, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d862, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8989 pattern childGuard
    simpa only [d862, d1056, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8991 (pattern : Twelve) (guard : d1848 pattern = 1) : d863 pattern ≤ (0 : Int) + d1057 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d863, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8977 pattern childGuard
    simpa only [d863, d1057, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d863, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d863, d1057, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8992 (pattern : Twelve) (guard : d1848 pattern = 1) : d867 pattern ≤ (0 : Int) + d1061 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d867, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8990 pattern childGuard
    simpa only [d867, d1061, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d867, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8991 pattern childGuard
    simpa only [d867, d1061, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8993 (pattern : Twelve) (guard : d1848 pattern = 1) : d869 pattern ≤ (0 : Int) + d1064 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d869, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8979 pattern childGuard
    simpa only [d869, d1064, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d869, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8992 pattern childGuard
    simpa only [d869, d1064, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8994 (pattern : Twelve) (guard : d1848 pattern = 1) : d861 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4236 pattern childGuard
    simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8977 pattern childGuard
    simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8995 (pattern : Twelve) (guard : d1848 pattern = 1) : d842 pattern ≤ (0 : Int) + d1042 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d842, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d842, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d842, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8981 pattern childGuard
    simpa only [d842, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8996 (pattern : Twelve) (guard : d1848 pattern = 1) : d855 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d855, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8995 pattern childGuard
    simpa only [d855, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d855, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8983 pattern childGuard
    simpa only [d855, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8997 (pattern : Twelve) (guard : d1848 pattern = 1) : d862 pattern ≤ (0 : Int) + d1058 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d862, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8996 pattern childGuard
    simpa only [d862, d1058, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d862, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8989 pattern childGuard
    simpa only [d862, d1058, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8998 (pattern : Twelve) (guard : d1848 pattern = 1) : d867 pattern ≤ (0 : Int) + d1062 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d867, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8997 pattern childGuard
    simpa only [d867, d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d867, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8991 pattern childGuard
    simpa only [d867, d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8999 (pattern : Twelve) (guard : d1848 pattern = 1) : d869 pattern ≤ (0 : Int) + d1065 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d869, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8994 pattern childGuard
    simpa only [d869, d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d869, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8998 pattern childGuard
    simpa only [d869, d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9000 (pattern : Twelve) (guard : d1848 pattern = 1) : d869 pattern ≤ (0 : Int) + d1067 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8993 pattern childGuard
    simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8999 pattern childGuard
    simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9001 (pattern : Twelve) (guard : d1848 pattern = 1) : d869 pattern ≤ (0 : Int) + d1068 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9000 pattern childGuard
    simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8999 pattern childGuard
    simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9002 (pattern : Twelve) (guard : d1848 pattern = 1) : d874 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d874, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d874, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d874, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c325 pattern childGuard
    simpa only [d1848, d874, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9003 (pattern : Twelve) (guard : d1848 pattern = 1) : d875 pattern ≤ (0 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d875, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d1848, d875, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d875, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c325 pattern childGuard
    simpa only [d1848, d875, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9004 (pattern : Twelve) (guard : d1848 pattern = 1) : d882 pattern ≤ (0 : Int) + d1033 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d882, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9002 pattern childGuard
    simpa only [d882, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d882, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9003 pattern childGuard
    simpa only [d882, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9005 (pattern : Twelve) (guard : d1848 pattern = 1) : d890 pattern ≤ (0 : Int) + d1042 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d890, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1354 pattern childGuard
    simpa only [d890, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d890, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9004 pattern childGuard
    simpa only [d890, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9006 (pattern : Twelve) (guard : d1848 pattern = 1) : d876 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d876, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d876, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d876, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1431 pattern childGuard
    simpa only [d1848, d876, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9007 (pattern : Twelve) (guard : d1848 pattern = 1) : d883 pattern ≤ (0 : Int) + d1032 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d883, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9006 pattern childGuard
    simpa only [d883, d1032, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d883, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2806 pattern childGuard
    simpa only [d883, d1032, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9008 (pattern : Twelve) (guard : d1848 pattern = 1) : d891 pattern ≤ (0 : Int) + d1041 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d891, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1418 pattern childGuard
    simpa only [d891, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d891, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9007 pattern childGuard
    simpa only [d891, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9009 (pattern : Twelve) (guard : d1848 pattern = 1) : d898 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d898, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9005 pattern childGuard
    simpa only [d898, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d898, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9008 pattern childGuard
    simpa only [d898, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9010 (pattern : Twelve) (guard : d0 pattern = 1) : d815 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9011 (pattern : Twelve) (guard : d1848 pattern = 1) : d877 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d877, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d877, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d877, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9010 pattern childGuard
    simpa only [d1848, d877, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9012 (pattern : Twelve) (guard : d1848 pattern = 1) : d884 pattern ≤ (0 : Int) + d1033 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d884, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9011 pattern childGuard
    simpa only [d884, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d884, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5577 pattern childGuard
    simpa only [d884, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9013 (pattern : Twelve) (guard : d1848 pattern = 1) : d892 pattern ≤ (0 : Int) + d1042 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d892, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2589 pattern childGuard
    simpa only [d892, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d892, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9012 pattern childGuard
    simpa only [d892, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9014 (pattern : Twelve) (guard : d1848 pattern = 1) : d893 pattern ≤ (0 : Int) + d1041 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d893, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2753 pattern childGuard
    simpa only [d893, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d893, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9007 pattern childGuard
    simpa only [d893, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9015 (pattern : Twelve) (guard : d1848 pattern = 1) : d899 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d899, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9013 pattern childGuard
    simpa only [d899, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d899, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9014 pattern childGuard
    simpa only [d899, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9016 (pattern : Twelve) (guard : d1848 pattern = 1) : d902 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9009 pattern childGuard
    simpa only [d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9015 pattern childGuard
    simpa only [d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9017 (pattern : Twelve) (guard : d1848 pattern = 1) : d878 pattern ≤ (0 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d878, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d1848, d878, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d878, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1341 pattern childGuard
    simpa only [d1848, d878, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9018 (pattern : Twelve) (guard : d1848 pattern = 1) : d885 pattern ≤ (0 : Int) + d1033 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d885, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9011 pattern childGuard
    simpa only [d885, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d885, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9017 pattern childGuard
    simpa only [d885, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9019 (pattern : Twelve) (guard : d1848 pattern = 1) : d894 pattern ≤ (0 : Int) + d1042 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d894, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d894, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d894, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9018 pattern childGuard
    simpa only [d894, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9020 (pattern : Twelve) (guard : d1848 pattern = 1) : d895 pattern ≤ (0 : Int) + d1041 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d895, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6658 pattern childGuard
    simpa only [d895, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d895, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9007 pattern childGuard
    simpa only [d895, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9021 (pattern : Twelve) (guard : d1848 pattern = 1) : d900 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d900, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9019 pattern childGuard
    simpa only [d900, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d900, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9020 pattern childGuard
    simpa only [d900, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9022 (pattern : Twelve) (guard : d1848 pattern = 1) : d887 pattern ≤ (0 : Int) + d1036 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d887, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8962 pattern childGuard
    simpa only [d887, d1036, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d887, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5636 pattern childGuard
    simpa only [d887, d1036, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9023 (pattern : Twelve) (guard : d1848 pattern = 1) : d896 pattern ≤ (0 : Int) + d1046 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d896, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d896, d1046, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d896, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9022 pattern childGuard
    simpa only [d896, d1046, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9024 (pattern : Twelve) (guard : d1848 pattern = 1) : d897 pattern ≤ (0 : Int) + d1047 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d897, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6665 pattern childGuard
    simpa only [d897, d1047, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d897, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5639 pattern childGuard
    simpa only [d897, d1047, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9025 (pattern : Twelve) (guard : d1848 pattern = 1) : d901 pattern ≤ (0 : Int) + d1053 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d901, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9023 pattern childGuard
    simpa only [d901, d1053, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d901, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9024 pattern childGuard
    simpa only [d901, d1053, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9026 (pattern : Twelve) (guard : d1848 pattern = 1) : d903 pattern ≤ (0 : Int) + d1059 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d903, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9021 pattern childGuard
    simpa only [d903, d1059, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d903, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9025 pattern childGuard
    simpa only [d903, d1059, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9027 (pattern : Twelve) (guard : d1848 pattern = 1) : d904 pattern ≤ (0 : Int) + d1057 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d904, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9015 pattern childGuard
    simpa only [d904, d1057, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d904, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d904, d1057, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9028 (pattern : Twelve) (guard : d1848 pattern = 1) : d905 pattern ≤ (0 : Int) + d1063 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d905, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9026 pattern childGuard
    simpa only [d905, d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d905, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9027 pattern childGuard
    simpa only [d905, d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9029 (pattern : Twelve) (guard : d1848 pattern = 1) : d906 pattern ≤ (0 : Int) + d1066 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d906, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9016 pattern childGuard
    simpa only [d906, d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d906, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9028 pattern childGuard
    simpa only [d906, d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9030 (pattern : Twelve) (guard : d1848 pattern = 1) : d907 pattern ≤ (0 : Int) + d1069 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d907, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9001 pattern childGuard
    simpa only [d907, d1069, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d907, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9029 pattern childGuard
    simpa only [d907, d1069, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9031 (pattern : Twelve) (guard : d1848 pattern = 1) : d1285 pattern ≤ (0 : Int) + d1445 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1285, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1478 pattern childGuard
    simpa only [d1285, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1285, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5652 pattern childGuard
    simpa only [d1285, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9032 (pattern : Twelve) (guard : d1848 pattern = 1) : d1295 pattern ≤ (0 : Int) + d1450 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1295, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2753 pattern childGuard
    simpa only [d1295, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1295, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9031 pattern childGuard
    simpa only [d1295, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9033 (pattern : Twelve) (guard : d1848 pattern = 1) : d1296 pattern ≤ (0 : Int) + d1449 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1296, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2796 pattern childGuard
    simpa only [d1296, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1296, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1296, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9034 (pattern : Twelve) (guard : d1848 pattern = 1) : d1306 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1306, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9032 pattern childGuard
    simpa only [d1306, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1306, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9033 pattern childGuard
    simpa only [d1306, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9035 (pattern : Twelve) (guard : d1848 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1459 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1313, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4271 pattern childGuard
    simpa only [d1313, d1459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1313, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9034 pattern childGuard
    simpa only [d1313, d1459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9036 (pattern : Twelve) (guard : d1848 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4275 pattern childGuard
    simpa only [d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9034 pattern childGuard
    simpa only [d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9037 (pattern : Twelve) (guard : d1848 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1463 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9035 pattern childGuard
    simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9036 pattern childGuard
    simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9038 (pattern : Twelve) (guard : d1848 pattern = 1) : d1281 pattern ≤ (0 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1281, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4265 pattern childGuard
    simpa only [d1848, d1281, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1281, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6656 pattern childGuard
    simpa only [d1848, d1281, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9039 (pattern : Twelve) (guard : d1848 pattern = 1) : d1287 pattern ≤ (0 : Int) + d1445 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1287, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1478 pattern childGuard
    simpa only [d1287, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1287, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9038 pattern childGuard
    simpa only [d1287, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9040 (pattern : Twelve) (guard : d1848 pattern = 1) : d1297 pattern ≤ (0 : Int) + d1450 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1297, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d1297, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1297, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9039 pattern childGuard
    simpa only [d1297, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9041 (pattern : Twelve) (guard : d1848 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1449 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1298, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1405 pattern childGuard
    simpa only [d1298, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1298, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1298, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9042 (pattern : Twelve) (guard : d1848 pattern = 1) : d1307 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1307, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9040 pattern childGuard
    simpa only [d1307, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1307, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9041 pattern childGuard
    simpa only [d1307, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9043 (pattern : Twelve) (guard : d1848 pattern = 1) : d1288 pattern ≤ (0 : Int) + d1446 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1288, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1491 pattern childGuard
    simpa only [d1288, d1446, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1288, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5401 pattern childGuard
    simpa only [d1288, d1446, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9044 (pattern : Twelve) (guard : d1848 pattern = 1) : d1299 pattern ≤ (0 : Int) + d1451 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1299, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2769 pattern childGuard
    simpa only [d1299, d1451, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1299, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9043 pattern childGuard
    simpa only [d1299, d1451, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9045 (pattern : Twelve) (guard : d1848 pattern = 1) : d1300 pattern ≤ (0 : Int) + d1452 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1300, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2807 pattern childGuard
    simpa only [d1300, d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1300, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1300, d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9046 (pattern : Twelve) (guard : d1848 pattern = 1) : d1308 pattern ≤ (0 : Int) + d1457 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1308, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9044 pattern childGuard
    simpa only [d1308, d1457, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1308, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9045 pattern childGuard
    simpa only [d1308, d1457, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9047 (pattern : Twelve) (guard : d1848 pattern = 1) : d1314 pattern ≤ (0 : Int) + d1460 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1314, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9042 pattern childGuard
    simpa only [d1314, d1460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1314, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9046 pattern childGuard
    simpa only [d1314, d1460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9048 (pattern : Twelve) (guard : d1848 pattern = 1) : d1315 pattern ≤ (0 : Int) + d1461 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1315, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9034 pattern childGuard
    simpa only [d1315, d1461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1315, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1315, d1461, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9049 (pattern : Twelve) (guard : d1848 pattern = 1) : d1319 pattern ≤ (0 : Int) + d1464 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1319, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9047 pattern childGuard
    simpa only [d1319, d1464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1319, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9048 pattern childGuard
    simpa only [d1319, d1464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9050 (pattern : Twelve) (guard : d1848 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1466 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1321, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9037 pattern childGuard
    simpa only [d1321, d1466, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1321, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9049 pattern childGuard
    simpa only [d1321, d1466, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9051 (pattern : Twelve) (guard : d1848 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1467 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1321, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9036 pattern childGuard
    simpa only [d1321, d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1321, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9049 pattern childGuard
    simpa only [d1321, d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9052 (pattern : Twelve) (guard : d1848 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1469 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9050 pattern childGuard
    simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9051 pattern childGuard
    simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9053 (pattern : Twelve) (guard : d1848 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1470 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9052 pattern childGuard
    simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9051 pattern childGuard
    simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9054 (pattern : Twelve) (guard : d1848 pattern = 1) : d1325 pattern ≤ (0 : Int) + d1444 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1325, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1469 pattern childGuard
    simpa only [d1848, d1325, d1444, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1325, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c389 pattern childGuard
    simpa only [d1848, d1325, d1444, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9055 (pattern : Twelve) (guard : d1848 pattern = 1) : d1326 pattern ≤ (0 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1326, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4265 pattern childGuard
    simpa only [d1848, d1326, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1326, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c389 pattern childGuard
    simpa only [d1848, d1326, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9056 (pattern : Twelve) (guard : d1848 pattern = 1) : d1333 pattern ≤ (0 : Int) + d1445 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1333, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9054 pattern childGuard
    simpa only [d1333, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1333, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9055 pattern childGuard
    simpa only [d1333, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9057 (pattern : Twelve) (guard : d1848 pattern = 1) : d1339 pattern ≤ (0 : Int) + d1450 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1339, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1418 pattern childGuard
    simpa only [d1339, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1339, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9056 pattern childGuard
    simpa only [d1339, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9058 (pattern : Twelve) (guard : d1848 pattern = 1) : d1345 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1345, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9057 pattern childGuard
    simpa only [d1345, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1345, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4270 pattern childGuard
    simpa only [d1345, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9059 (pattern : Twelve) (guard : d1848 pattern = 1) : d1327 pattern ≤ (0 : Int) + d1444 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1327, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1469 pattern childGuard
    simpa only [d1848, d1327, d1444, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1327, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6656 pattern childGuard
    simpa only [d1848, d1327, d1444, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9060 (pattern : Twelve) (guard : d1848 pattern = 1) : d1334 pattern ≤ (0 : Int) + d1445 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1334, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9059 pattern childGuard
    simpa only [d1334, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1334, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5652 pattern childGuard
    simpa only [d1334, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9061 (pattern : Twelve) (guard : d1848 pattern = 1) : d1340 pattern ≤ (0 : Int) + d1450 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1340, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2753 pattern childGuard
    simpa only [d1340, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1340, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9060 pattern childGuard
    simpa only [d1340, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9062 (pattern : Twelve) (guard : d1848 pattern = 1) : d1346 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1346, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9061 pattern childGuard
    simpa only [d1346, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1346, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9033 pattern childGuard
    simpa only [d1346, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9063 (pattern : Twelve) (guard : d1848 pattern = 1) : d1349 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9058 pattern childGuard
    simpa only [d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9062 pattern childGuard
    simpa only [d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9064 (pattern : Twelve) (guard : d1848 pattern = 1) : d1328 pattern ≤ (0 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1328, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4265 pattern childGuard
    simpa only [d1848, d1328, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1328, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1490 pattern childGuard
    simpa only [d1848, d1328, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9065 (pattern : Twelve) (guard : d1848 pattern = 1) : d1335 pattern ≤ (0 : Int) + d1445 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1335, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9059 pattern childGuard
    simpa only [d1335, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1335, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9064 pattern childGuard
    simpa only [d1335, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9066 (pattern : Twelve) (guard : d1848 pattern = 1) : d1341 pattern ≤ (0 : Int) + d1450 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1341, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d1341, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1341, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9065 pattern childGuard
    simpa only [d1341, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9067 (pattern : Twelve) (guard : d1848 pattern = 1) : d1342 pattern ≤ (0 : Int) + d1449 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1342, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6700 pattern childGuard
    simpa only [d1342, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1342, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1342, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9068 (pattern : Twelve) (guard : d1848 pattern = 1) : d1347 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1347, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9066 pattern childGuard
    simpa only [d1347, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1347, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9067 pattern childGuard
    simpa only [d1347, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9069 (pattern : Twelve) (guard : d1848 pattern = 1) : d1343 pattern ≤ (0 : Int) + d1453 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1343, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2769 pattern childGuard
    simpa only [d1343, d1453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1343, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5693 pattern childGuard
    simpa only [d1343, d1453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9070 (pattern : Twelve) (guard : d1848 pattern = 1) : d1344 pattern ≤ (0 : Int) + d1454 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1344, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6705 pattern childGuard
    simpa only [d1344, d1454, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1344, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1344, d1454, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9071 (pattern : Twelve) (guard : d1848 pattern = 1) : d1348 pattern ≤ (0 : Int) + d1458 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1348, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9069 pattern childGuard
    simpa only [d1348, d1458, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1348, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9070 pattern childGuard
    simpa only [d1348, d1458, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9072 (pattern : Twelve) (guard : d1848 pattern = 1) : d1350 pattern ≤ (0 : Int) + d1462 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1350, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9068 pattern childGuard
    simpa only [d1350, d1462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1350, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9071 pattern childGuard
    simpa only [d1350, d1462, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9073 (pattern : Twelve) (guard : d1848 pattern = 1) : d1351 pattern ≤ (0 : Int) + d1461 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1351, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9062 pattern childGuard
    simpa only [d1351, d1461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1351, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1351, d1461, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9074 (pattern : Twelve) (guard : d1848 pattern = 1) : d1352 pattern ≤ (0 : Int) + d1465 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1352, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9072 pattern childGuard
    simpa only [d1352, d1465, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1352, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9073 pattern childGuard
    simpa only [d1352, d1465, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9075 (pattern : Twelve) (guard : d1848 pattern = 1) : d1353 pattern ≤ (0 : Int) + d1468 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1353, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9063 pattern childGuard
    simpa only [d1353, d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1353, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9074 pattern childGuard
    simpa only [d1353, d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9076 (pattern : Twelve) (guard : d1848 pattern = 1) : d1354 pattern ≤ (0 : Int) + d1471 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1354, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9053 pattern childGuard
    simpa only [d1354, d1471, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1354, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9075 pattern childGuard
    simpa only [d1354, d1471, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9077 (pattern : Twelve) (guard : d1848 pattern = 1) : d1647 pattern ≤ (0 : Int) + d1645 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1531 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5705 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9078 (pattern : Twelve) (guard : d1848 pattern = 1) : d1651 pattern ≤ (0 : Int) + d1716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1651, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2796 pattern childGuard
    simpa only [d1651, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1651, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9077 pattern childGuard
    simpa only [d1651, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9079 (pattern : Twelve) (guard : d1848 pattern = 1) : d1657 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1657, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9078 pattern childGuard
    simpa only [d1657, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1657, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9045 pattern childGuard
    simpa only [d1657, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9080 (pattern : Twelve) (guard : d1848 pattern = 1) : d1660 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4306 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9079 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9081 (pattern : Twelve) (guard : d1848 pattern = 1) : d1652 pattern ≤ (0 : Int) + d1716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1652, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1405 pattern childGuard
    simpa only [d1652, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1652, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1531 pattern childGuard
    simpa only [d1652, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9082 (pattern : Twelve) (guard : d1848 pattern = 1) : d1653 pattern ≤ (0 : Int) + d1452 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1653, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1432 pattern childGuard
    simpa only [d1653, d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1653, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1653, d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9083 (pattern : Twelve) (guard : d1848 pattern = 1) : d1658 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1658, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9081 pattern childGuard
    simpa only [d1658, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1658, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9082 pattern childGuard
    simpa only [d1658, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9084 (pattern : Twelve) (guard : d1848 pattern = 1) : d1648 pattern ≤ (0 : Int) + d128 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1538 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5446 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9085 (pattern : Twelve) (guard : d1848 pattern = 1) : d1654 pattern ≤ (0 : Int) + d1717 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1654, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2807 pattern childGuard
    simpa only [d1654, d1717, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1654, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9084 pattern childGuard
    simpa only [d1654, d1717, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9086 (pattern : Twelve) (guard : d1848 pattern = 1) : d1659 pattern ≤ (0 : Int) + d1720 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1659, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9085 pattern childGuard
    simpa only [d1659, d1720, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1659, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5715 pattern childGuard
    simpa only [d1659, d1720, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9087 (pattern : Twelve) (guard : d1848 pattern = 1) : d1661 pattern ≤ (0 : Int) + d1722 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1661, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9083 pattern childGuard
    simpa only [d1661, d1722, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1661, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9086 pattern childGuard
    simpa only [d1661, d1722, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9088 (pattern : Twelve) (guard : d1848 pattern = 1) : d1662 pattern ≤ (0 : Int) + d1723 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1662, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9079 pattern childGuard
    simpa only [d1662, d1723, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1662, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1662, d1723, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9089 (pattern : Twelve) (guard : d1848 pattern = 1) : d1663 pattern ≤ (0 : Int) + d1725 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1663, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9087 pattern childGuard
    simpa only [d1663, d1725, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1663, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9088 pattern childGuard
    simpa only [d1663, d1725, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9090 (pattern : Twelve) (guard : d1848 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1727 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1664, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9080 pattern childGuard
    simpa only [d1664, d1727, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1664, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9089 pattern childGuard
    simpa only [d1664, d1727, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9091 (pattern : Twelve) (guard : d1848 pattern = 1) : d1668 pattern ≤ (0 : Int) + d1716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1668, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1473 pattern childGuard
    simpa only [d1668, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1668, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1531 pattern childGuard
    simpa only [d1668, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9092 (pattern : Twelve) (guard : d1848 pattern = 1) : d1671 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1671, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9091 pattern childGuard
    simpa only [d1671, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1671, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4305 pattern childGuard
    simpa only [d1671, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9093 (pattern : Twelve) (guard : d1848 pattern = 1) : d1674 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9092 pattern childGuard
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9079 pattern childGuard
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9094 (pattern : Twelve) (guard : d1848 pattern = 1) : d1665 pattern ≤ (0 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1665, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c388 pattern childGuard
    simpa only [d1848, d1665, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1665, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1537 pattern childGuard
    simpa only [d1848, d1665, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9095 (pattern : Twelve) (guard : d1848 pattern = 1) : d1666 pattern ≤ (0 : Int) + d1645 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1531 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9094 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9096 (pattern : Twelve) (guard : d1848 pattern = 1) : d1669 pattern ≤ (0 : Int) + d1716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1669, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1405 pattern childGuard
    simpa only [d1669, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1669, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9095 pattern childGuard
    simpa only [d1669, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9097 (pattern : Twelve) (guard : d1848 pattern = 1) : d1672 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1672, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9096 pattern childGuard
    simpa only [d1672, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1672, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9045 pattern childGuard
    simpa only [d1672, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9098 (pattern : Twelve) (guard : d1848 pattern = 1) : d1670 pattern ≤ (0 : Int) + d1718 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1670, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2807 pattern childGuard
    simpa only [d1670, d1718, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1670, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5728 pattern childGuard
    simpa only [d1670, d1718, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9099 (pattern : Twelve) (guard : d1848 pattern = 1) : d1673 pattern ≤ (0 : Int) + d1721 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1673, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9098 pattern childGuard
    simpa only [d1673, d1721, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1673, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5730 pattern childGuard
    simpa only [d1673, d1721, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
