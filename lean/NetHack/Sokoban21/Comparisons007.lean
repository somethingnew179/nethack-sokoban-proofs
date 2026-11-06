/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons006
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c980 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c981 (pattern : Twelve) (guard : d1837 pattern = 1) : d944 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1837, d944, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c980 pattern childGuard
    simpa only [d1837, d944, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c982 (pattern : Twelve) (guard : d1837 pattern = 1) : d951 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d951, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c981 pattern childGuard
    simpa only [d951, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d951, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c965 pattern childGuard
    simpa only [d951, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c983 (pattern : Twelve) (guard : d1837 pattern = 1) : d957 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d957, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c979 pattern childGuard
    simpa only [d957, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d957, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c982 pattern childGuard
    simpa only [d957, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c984 (pattern : Twelve) (guard : d1837 pattern = 1) : d263 pattern ≤ (0 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c848 pattern childGuard
    simpa only [d263, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c971 pattern childGuard
    simpa only [d263, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c985 (pattern : Twelve) (guard : d1837 pattern = 1) : d958 pattern ≤ (0 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d958, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c984 pattern childGuard
    simpa only [d958, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d958, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c974 pattern childGuard
    simpa only [d958, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c986 (pattern : Twelve) (guard : d1837 pattern = 1) : d964 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d964, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c983 pattern childGuard
    simpa only [d964, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d964, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c985 pattern childGuard
    simpa only [d964, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c987 (pattern : Twelve) (guard : d1837 pattern = 1) : d970 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c976 pattern childGuard
    simpa only [d970, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c986 pattern childGuard
    simpa only [d970, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c988 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d819 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c989 (pattern : Twelve) (guard : d1837 pattern = 1) : d241 pattern ≤ (0 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d241, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d241, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d241, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c988 pattern childGuard
    simpa only [d1837, d241, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c990 (pattern : Twelve) (guard : d1837 pattern = 1) : d265 pattern ≤ (0 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d265, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c859 pattern childGuard
    simpa only [d265, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d265, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c989 pattern childGuard
    simpa only [d265, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c991 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d34 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c992 (pattern : Twelve) (guard : d1837 pattern = 1) : d241 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c991 pattern childGuard
    simpa only [d1837, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c993 (pattern : Twelve) (guard : d1837 pattern = 1) : d949 pattern ≤ (0 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d949, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c992 pattern childGuard
    simpa only [d949, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d949, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c965 pattern childGuard
    simpa only [d949, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c994 (pattern : Twelve) (guard : d1837 pattern = 1) : d959 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d959, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c990 pattern childGuard
    simpa only [d959, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d959, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c993 pattern childGuard
    simpa only [d959, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c995 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d820 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c996 (pattern : Twelve) (guard : d1837 pattern = 1) : d251 pattern ≤ (0 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d251, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c143 pattern childGuard
    simpa only [d1837, d251, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d251, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c995 pattern childGuard
    simpa only [d1837, d251, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c997 (pattern : Twelve) (guard : d1837 pattern = 1) : d267 pattern ≤ (0 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d267, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c868 pattern childGuard
    simpa only [d267, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d267, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c996 pattern childGuard
    simpa only [d267, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c998 (pattern : Twelve) (guard : d1837 pattern = 1) : d251 pattern ≤ (0 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d251, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c143 pattern childGuard
    simpa only [d1837, d251, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d251, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c864 pattern childGuard
    simpa only [d1837, d251, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c999 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d822 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1000 (pattern : Twelve) (guard : d1837 pattern = 1) : d945 pattern ≤ (0 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d945, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c278 pattern childGuard
    simpa only [d1837, d945, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d945, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c999 pattern childGuard
    simpa only [d1837, d945, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1001 (pattern : Twelve) (guard : d1837 pattern = 1) : d952 pattern ≤ (0 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d952, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c998 pattern childGuard
    simpa only [d952, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d952, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1000 pattern childGuard
    simpa only [d952, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1002 (pattern : Twelve) (guard : d1837 pattern = 1) : d960 pattern ≤ (0 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d960, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c997 pattern childGuard
    simpa only [d960, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d960, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1001 pattern childGuard
    simpa only [d960, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1003 (pattern : Twelve) (guard : d1837 pattern = 1) : d965 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d965, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c994 pattern childGuard
    simpa only [d965, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d965, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1002 pattern childGuard
    simpa only [d965, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1004 (pattern : Twelve) (guard : d1837 pattern = 1) : d966 pattern ≤ (0 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d966, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c985 pattern childGuard
    simpa only [d966, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d966, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d966, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1005 (pattern : Twelve) (guard : d1837 pattern = 1) : d971 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d971, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1003 pattern childGuard
    simpa only [d971, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d971, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1004 pattern childGuard
    simpa only [d971, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1006 (pattern : Twelve) (guard : d1837 pattern = 1) : d973 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d973, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c987 pattern childGuard
    simpa only [d973, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d973, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1005 pattern childGuard
    simpa only [d973, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1007 (pattern : Twelve) (guard : d1837 pattern = 1) : d953 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d953, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c882 pattern childGuard
    simpa only [d953, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d953, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c978 pattern childGuard
    simpa only [d953, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1008 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d823 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1009 (pattern : Twelve) (guard : d1837 pattern = 1) : d946 pattern ≤ (0 : Int) + d823 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c288 pattern childGuard
    simpa only [d1837, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1008 pattern childGuard
    simpa only [d1837, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1010 (pattern : Twelve) (guard : d1837 pattern = 1) : d954 pattern ≤ (0 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d954, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1009 pattern childGuard
    simpa only [d954, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d954, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c965 pattern childGuard
    simpa only [d954, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1011 (pattern : Twelve) (guard : d1837 pattern = 1) : d961 pattern ≤ (0 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d961, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1007 pattern childGuard
    simpa only [d961, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d961, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1010 pattern childGuard
    simpa only [d961, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1012 (pattern : Twelve) (guard : d1837 pattern = 1) : d241 pattern ≤ (0 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d241, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d241, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d241, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c901 pattern childGuard
    simpa only [d1837, d241, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1013 (pattern : Twelve) (guard : d1837 pattern = 1) : d263 pattern ≤ (0 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c848 pattern childGuard
    simpa only [d263, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1012 pattern childGuard
    simpa only [d263, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1014 (pattern : Twelve) (guard : d1837 pattern = 1) : d241 pattern ≤ (0 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d241, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d241, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d241, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c867 pattern childGuard
    simpa only [d1837, d241, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1015 (pattern : Twelve) (guard : d1837 pattern = 1) : d949 pattern ≤ (0 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d949, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1014 pattern childGuard
    simpa only [d949, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d949, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c965 pattern childGuard
    simpa only [d949, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1016 (pattern : Twelve) (guard : d1837 pattern = 1) : d958 pattern ≤ (0 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d958, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1013 pattern childGuard
    simpa only [d958, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d958, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1015 pattern childGuard
    simpa only [d958, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1017 (pattern : Twelve) (guard : d1837 pattern = 1) : d967 pattern ≤ (0 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d967, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1011 pattern childGuard
    simpa only [d967, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d967, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1016 pattern childGuard
    simpa only [d967, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1018 (pattern : Twelve) (guard : d1837 pattern = 1) : d241 pattern ≤ (0 : Int) + d834 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d241, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d241, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d241, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c909 pattern childGuard
    simpa only [d1837, d241, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1019 (pattern : Twelve) (guard : d1837 pattern = 1) : d263 pattern ≤ (0 : Int) + d849 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c887 pattern childGuard
    simpa only [d263, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1018 pattern childGuard
    simpa only [d263, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1020 (pattern : Twelve) (guard : d1837 pattern = 1) : d241 pattern ≤ (0 : Int) + d835 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d241, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d241, d835, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d241, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c912 pattern childGuard
    simpa only [d1837, d241, d835, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1021 (pattern : Twelve) (guard : d1837 pattern = 1) : d949 pattern ≤ (0 : Int) + d850 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d949, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1020 pattern childGuard
    simpa only [d949, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d949, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c965 pattern childGuard
    simpa only [d949, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1022 (pattern : Twelve) (guard : d1837 pattern = 1) : d958 pattern ≤ (0 : Int) + d859 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d958, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1019 pattern childGuard
    simpa only [d958, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d958, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1021 pattern childGuard
    simpa only [d958, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1023 (pattern : Twelve) (guard : d1837 pattern = 1) : d251 pattern ≤ (0 : Int) + d836 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d251, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c143 pattern childGuard
    simpa only [d1837, d251, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d251, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c916 pattern childGuard
    simpa only [d1837, d251, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1024 (pattern : Twelve) (guard : d1837 pattern = 1) : d267 pattern ≤ (0 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d267, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c868 pattern childGuard
    simpa only [d267, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d267, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1023 pattern childGuard
    simpa only [d267, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1025 (pattern : Twelve) (guard : d1837 pattern = 1) : d251 pattern ≤ (0 : Int) + d837 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d251, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c143 pattern childGuard
    simpa only [d1837, d251, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d251, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c919 pattern childGuard
    simpa only [d1837, d251, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1026 (pattern : Twelve) (guard : d1837 pattern = 1) : d952 pattern ≤ (0 : Int) + d852 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d952, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1025 pattern childGuard
    simpa only [d952, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d952, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1000 pattern childGuard
    simpa only [d952, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1027 (pattern : Twelve) (guard : d1837 pattern = 1) : d960 pattern ≤ (0 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d960, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1024 pattern childGuard
    simpa only [d960, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d960, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1026 pattern childGuard
    simpa only [d960, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1028 (pattern : Twelve) (guard : d1837 pattern = 1) : d968 pattern ≤ (0 : Int) + d865 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d968, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1022 pattern childGuard
    simpa only [d968, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d968, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1027 pattern childGuard
    simpa only [d968, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1029 (pattern : Twelve) (guard : d1837 pattern = 1) : d966 pattern ≤ (0 : Int) + d866 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d966, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1016 pattern childGuard
    simpa only [d966, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d966, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d966, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1030 (pattern : Twelve) (guard : d1837 pattern = 1) : d972 pattern ≤ (0 : Int) + d868 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d972, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1028 pattern childGuard
    simpa only [d972, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d972, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1029 pattern childGuard
    simpa only [d972, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1031 (pattern : Twelve) (guard : d1837 pattern = 1) : d974 pattern ≤ (0 : Int) + d870 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d974, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1017 pattern childGuard
    simpa only [d974, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d974, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1030 pattern childGuard
    simpa only [d974, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1032 (pattern : Twelve) (guard : d1837 pattern = 1) : d976 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d976, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1006 pattern childGuard
    simpa only [d976, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d976, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1031 pattern childGuard
    simpa only [d976, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1033 (pattern : Twelve) (guard : d1837 pattern = 1) : d962 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d962, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1007 pattern childGuard
    simpa only [d962, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d962, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c982 pattern childGuard
    simpa only [d962, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1034 (pattern : Twelve) (guard : d1837 pattern = 1) : d969 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d969, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1033 pattern childGuard
    simpa only [d969, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d969, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c985 pattern childGuard
    simpa only [d969, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1035 (pattern : Twelve) (guard : d1837 pattern = 1) : d263 pattern ≤ (0 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c887 pattern childGuard
    simpa only [d263, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c989 pattern childGuard
    simpa only [d263, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1036 (pattern : Twelve) (guard : d1837 pattern = 1) : d958 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d958, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1035 pattern childGuard
    simpa only [d958, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d958, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c993 pattern childGuard
    simpa only [d958, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1037 (pattern : Twelve) (guard : d1837 pattern = 1) : d968 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d968, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1036 pattern childGuard
    simpa only [d968, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d968, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1002 pattern childGuard
    simpa only [d968, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1038 (pattern : Twelve) (guard : d1837 pattern = 1) : d972 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d972, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1037 pattern childGuard
    simpa only [d972, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d972, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1004 pattern childGuard
    simpa only [d972, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1039 (pattern : Twelve) (guard : d1837 pattern = 1) : d975 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d975, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1034 pattern childGuard
    simpa only [d975, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d975, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1038 pattern childGuard
    simpa only [d975, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1040 (pattern : Twelve) (guard : d1837 pattern = 1) : d977 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d977, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1039 pattern childGuard
    simpa only [d977, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d977, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1031 pattern childGuard
    simpa only [d977, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1041 (pattern : Twelve) (guard : d1837 pattern = 1) : d978 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1032 pattern childGuard
    simpa only [d978, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1040 pattern childGuard
    simpa only [d978, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1042 (pattern : Twelve) (guard : d1837 pattern = 1) : d979 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1041 pattern childGuard
    simpa only [d979, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1040 pattern childGuard
    simpa only [d979, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1043 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1044 (pattern : Twelve) (guard : d1837 pattern = 1) : d1380 pattern ≤ (0 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1380, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c324 pattern childGuard
    simpa only [d1837, d1380, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1380, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1043 pattern childGuard
    simpa only [d1837, d1380, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1045 (pattern : Twelve) (guard : d1837 pattern = 1) : d1385 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1385, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c964 pattern childGuard
    simpa only [d1385, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1385, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1044 pattern childGuard
    simpa only [d1385, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1046 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1047 (pattern : Twelve) (guard : d1837 pattern = 1) : d1381 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1837, d1381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1046 pattern childGuard
    simpa only [d1837, d1381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1048 (pattern : Twelve) (guard : d1837 pattern = 1) : d1386 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1386, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1047 pattern childGuard
    simpa only [d1386, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1386, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1386, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1049 (pattern : Twelve) (guard : d1837 pattern = 1) : d1393 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1393, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1045 pattern childGuard
    simpa only [d1393, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1393, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1048 pattern childGuard
    simpa only [d1393, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1050 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1280 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1051 (pattern : Twelve) (guard : d1837 pattern = 1) : d1382 pattern ≤ (0 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1382, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c333 pattern childGuard
    simpa only [d1837, d1382, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1382, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1050 pattern childGuard
    simpa only [d1837, d1382, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1052 (pattern : Twelve) (guard : d1837 pattern = 1) : d1387 pattern ≤ (0 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1387, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c973 pattern childGuard
    simpa only [d1387, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1387, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1051 pattern childGuard
    simpa only [d1387, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1053 (pattern : Twelve) (guard : d1837 pattern = 1) : d942 pattern ≤ (0 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d942, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d1837, d942, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d942, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c828 pattern childGuard
    simpa only [d1837, d942, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1054 (pattern : Twelve) (guard : d1837 pattern = 1) : d1388 pattern ≤ (0 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1388, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1053 pattern childGuard
    simpa only [d1388, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1388, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1388, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1055 (pattern : Twelve) (guard : d1837 pattern = 1) : d1394 pattern ≤ (0 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1394, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1052 pattern childGuard
    simpa only [d1394, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1394, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1054 pattern childGuard
    simpa only [d1394, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1056 (pattern : Twelve) (guard : d1837 pattern = 1) : d1398 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1398, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1049 pattern childGuard
    simpa only [d1398, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1398, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1055 pattern childGuard
    simpa only [d1398, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1057 (pattern : Twelve) (guard : d1837 pattern = 1) : d1389 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1389, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c981 pattern childGuard
    simpa only [d1389, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1389, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1044 pattern childGuard
    simpa only [d1389, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1058 (pattern : Twelve) (guard : d1837 pattern = 1) : d1395 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1395, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1057 pattern childGuard
    simpa only [d1395, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1395, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1048 pattern childGuard
    simpa only [d1395, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1059 (pattern : Twelve) (guard : d1837 pattern = 1) : d1399 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1399, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1058 pattern childGuard
    simpa only [d1399, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1399, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1055 pattern childGuard
    simpa only [d1399, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1060 (pattern : Twelve) (guard : d1837 pattern = 1) : d1403 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1056 pattern childGuard
    simpa only [d1403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1059 pattern childGuard
    simpa only [d1403, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1061 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1281 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1062 (pattern : Twelve) (guard : d1837 pattern = 1) : d1382 pattern ≤ (0 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1382, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c333 pattern childGuard
    simpa only [d1837, d1382, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1382, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1061 pattern childGuard
    simpa only [d1837, d1382, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1063 (pattern : Twelve) (guard : d1837 pattern = 1) : d1387 pattern ≤ (0 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1387, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c992 pattern childGuard
    simpa only [d1387, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1387, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1062 pattern childGuard
    simpa only [d1387, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1064 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d817 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1065 (pattern : Twelve) (guard : d1837 pattern = 1) : d942 pattern ≤ (0 : Int) + d817 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d1837, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1064 pattern childGuard
    simpa only [d1837, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1066 (pattern : Twelve) (guard : d1837 pattern = 1) : d1388 pattern ≤ (0 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1388, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1065 pattern childGuard
    simpa only [d1388, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1388, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1388, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1067 (pattern : Twelve) (guard : d1837 pattern = 1) : d1394 pattern ≤ (0 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1394, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1063 pattern childGuard
    simpa only [d1394, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1394, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1066 pattern childGuard
    simpa only [d1394, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1068 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d125 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1069 (pattern : Twelve) (guard : d1837 pattern = 1) : d1383 pattern ≤ (0 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1383, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c352 pattern childGuard
    simpa only [d1837, d1383, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1383, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1068 pattern childGuard
    simpa only [d1837, d1383, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1070 (pattern : Twelve) (guard : d1837 pattern = 1) : d1390 pattern ≤ (0 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1390, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c998 pattern childGuard
    simpa only [d1390, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1390, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1069 pattern childGuard
    simpa only [d1390, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1071 (pattern : Twelve) (guard : d1837 pattern = 1) : d945 pattern ≤ (0 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d945, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c278 pattern childGuard
    simpa only [d1837, d945, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d945, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c869 pattern childGuard
    simpa only [d1837, d945, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1072 (pattern : Twelve) (guard : d1837 pattern = 1) : d1391 pattern ≤ (0 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1391, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1071 pattern childGuard
    simpa only [d1391, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1391, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1391, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1073 (pattern : Twelve) (guard : d1837 pattern = 1) : d1396 pattern ≤ (0 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1396, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1070 pattern childGuard
    simpa only [d1396, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1396, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1072 pattern childGuard
    simpa only [d1396, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1074 (pattern : Twelve) (guard : d1837 pattern = 1) : d1400 pattern ≤ (0 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1400, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1067 pattern childGuard
    simpa only [d1400, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1400, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1073 pattern childGuard
    simpa only [d1400, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1075 (pattern : Twelve) (guard : d1837 pattern = 1) : d1401 pattern ≤ (0 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1401, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1055 pattern childGuard
    simpa only [d1401, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1401, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1401, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1076 (pattern : Twelve) (guard : d1837 pattern = 1) : d1404 pattern ≤ (0 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1404, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1074 pattern childGuard
    simpa only [d1404, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1404, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1075 pattern childGuard
    simpa only [d1404, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1077 (pattern : Twelve) (guard : d1837 pattern = 1) : d1405 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1405, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1060 pattern childGuard
    simpa only [d1405, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1405, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1076 pattern childGuard
    simpa only [d1405, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1078 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1283 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1079 (pattern : Twelve) (guard : d1837 pattern = 1) : d1384 pattern ≤ (0 : Int) + d1283 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c363 pattern childGuard
    simpa only [d1837, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1078 pattern childGuard
    simpa only [d1837, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1080 (pattern : Twelve) (guard : d1837 pattern = 1) : d1392 pattern ≤ (0 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1392, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1079 pattern childGuard
    simpa only [d1392, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1392, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1392, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1081 (pattern : Twelve) (guard : d1837 pattern = 1) : d1397 pattern ≤ (0 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1397, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1057 pattern childGuard
    simpa only [d1397, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1397, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1080 pattern childGuard
    simpa only [d1397, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1082 (pattern : Twelve) (guard : d1837 pattern = 1) : d942 pattern ≤ (0 : Int) + d1290 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d942, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d1837, d942, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d942, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c864 pattern childGuard
    simpa only [d1837, d942, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1083 (pattern : Twelve) (guard : d1837 pattern = 1) : d1388 pattern ≤ (0 : Int) + d1302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1388, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1082 pattern childGuard
    simpa only [d1388, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1388, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1388, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1084 (pattern : Twelve) (guard : d1837 pattern = 1) : d1394 pattern ≤ (0 : Int) + d1310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1394, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1052 pattern childGuard
    simpa only [d1394, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1394, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1083 pattern childGuard
    simpa only [d1394, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1085 (pattern : Twelve) (guard : d1837 pattern = 1) : d1402 pattern ≤ (0 : Int) + d1316 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1402, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1081 pattern childGuard
    simpa only [d1402, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1402, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1084 pattern childGuard
    simpa only [d1402, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1086 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d41 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1087 (pattern : Twelve) (guard : d1837 pattern = 1) : d942 pattern ≤ (0 : Int) + d1291 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d942, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d1837, d942, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d942, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1086 pattern childGuard
    simpa only [d1837, d942, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1088 (pattern : Twelve) (guard : d1837 pattern = 1) : d1388 pattern ≤ (0 : Int) + d1303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1388, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1087 pattern childGuard
    simpa only [d1388, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1388, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1388, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1089 (pattern : Twelve) (guard : d1837 pattern = 1) : d1394 pattern ≤ (0 : Int) + d1311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1394, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1063 pattern childGuard
    simpa only [d1394, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1394, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1088 pattern childGuard
    simpa only [d1394, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1090 (pattern : Twelve) (guard : d1837 pattern = 1) : d945 pattern ≤ (0 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d945, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c278 pattern childGuard
    simpa only [d1837, d945, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d945, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c921 pattern childGuard
    simpa only [d1837, d945, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1091 (pattern : Twelve) (guard : d1837 pattern = 1) : d1391 pattern ≤ (0 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1391, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1090 pattern childGuard
    simpa only [d1391, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1391, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1391, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1092 (pattern : Twelve) (guard : d1837 pattern = 1) : d1396 pattern ≤ (0 : Int) + d1312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1396, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1070 pattern childGuard
    simpa only [d1396, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1396, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1091 pattern childGuard
    simpa only [d1396, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1093 (pattern : Twelve) (guard : d1837 pattern = 1) : d1400 pattern ≤ (0 : Int) + d1317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1400, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1089 pattern childGuard
    simpa only [d1400, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1400, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1092 pattern childGuard
    simpa only [d1400, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1094 (pattern : Twelve) (guard : d1837 pattern = 1) : d1401 pattern ≤ (0 : Int) + d1318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1401, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1084 pattern childGuard
    simpa only [d1401, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1401, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1401, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1095 (pattern : Twelve) (guard : d1837 pattern = 1) : d1404 pattern ≤ (0 : Int) + d1320 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1404, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1093 pattern childGuard
    simpa only [d1404, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1404, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1094 pattern childGuard
    simpa only [d1404, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1096 (pattern : Twelve) (guard : d1837 pattern = 1) : d1406 pattern ≤ (0 : Int) + d1322 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1406, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1085 pattern childGuard
    simpa only [d1406, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1406, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1095 pattern childGuard
    simpa only [d1406, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1097 (pattern : Twelve) (guard : d1837 pattern = 1) : d1408 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1408, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1077 pattern childGuard
    simpa only [d1408, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1408, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1096 pattern childGuard
    simpa only [d1408, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1098 (pattern : Twelve) (guard : d1837 pattern = 1) : d1407 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1407, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1059 pattern childGuard
    simpa only [d1407, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1407, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1076 pattern childGuard
    simpa only [d1407, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1099 (pattern : Twelve) (guard : d1837 pattern = 1) : d1409 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1409, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1098 pattern childGuard
    simpa only [d1409, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1409, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1096 pattern childGuard
    simpa only [d1409, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1100 (pattern : Twelve) (guard : d1837 pattern = 1) : d1410 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1097 pattern childGuard
    simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1099 pattern childGuard
    simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1101 (pattern : Twelve) (guard : d1837 pattern = 1) : d1411 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1100 pattern childGuard
    simpa only [d1411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1099 pattern childGuard
    simpa only [d1411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1102 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1103 (pattern : Twelve) (guard : d1837 pattern = 1) : d1689 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c388 pattern childGuard
    simpa only [d1837, d1689, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1102 pattern childGuard
    simpa only [d1837, d1689, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1104 (pattern : Twelve) (guard : d1837 pattern = 1) : d1693 pattern ≤ (0 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1693, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1047 pattern childGuard
    simpa only [d1693, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1693, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1103 pattern childGuard
    simpa only [d1693, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1105 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1106 (pattern : Twelve) (guard : d1837 pattern = 1) : d1690 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c392 pattern childGuard
    simpa only [d1837, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1105 pattern childGuard
    simpa only [d1837, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1107 (pattern : Twelve) (guard : d1837 pattern = 1) : d1694 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1694, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1106 pattern childGuard
    simpa only [d1694, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1694, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1694, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1108 (pattern : Twelve) (guard : d1837 pattern = 1) : d1697 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1697, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1104 pattern childGuard
    simpa only [d1697, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1697, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1107 pattern childGuard
    simpa only [d1697, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1109 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1645 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1110 (pattern : Twelve) (guard : d1837 pattern = 1) : d1691 pattern ≤ (0 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1691, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c397 pattern childGuard
    simpa only [d1837, d1691, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1691, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1109 pattern childGuard
    simpa only [d1837, d1691, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1111 (pattern : Twelve) (guard : d1837 pattern = 1) : d1695 pattern ≤ (0 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1695, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1053 pattern childGuard
    simpa only [d1695, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1695, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1110 pattern childGuard
    simpa only [d1695, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1112 (pattern : Twelve) (guard : d1837 pattern = 1) : d1698 pattern ≤ (0 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1698, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1111 pattern childGuard
    simpa only [d1698, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1698, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1072 pattern childGuard
    simpa only [d1698, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1113 (pattern : Twelve) (guard : d1837 pattern = 1) : d1700 pattern ≤ (0 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1700, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1108 pattern childGuard
    simpa only [d1700, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1700, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1112 pattern childGuard
    simpa only [d1700, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1114 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1644 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1115 (pattern : Twelve) (guard : d1837 pattern = 1) : d1691 pattern ≤ (0 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c397 pattern childGuard
    simpa only [d1837, d1691, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1114 pattern childGuard
    simpa only [d1837, d1691, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1116 (pattern : Twelve) (guard : d1837 pattern = 1) : d1695 pattern ≤ (0 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1695, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1065 pattern childGuard
    simpa only [d1695, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1695, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1115 pattern childGuard
    simpa only [d1695, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1117 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d821 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1118 (pattern : Twelve) (guard : d1837 pattern = 1) : d945 pattern ≤ (0 : Int) + d821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c278 pattern childGuard
    simpa only [d1837, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1117 pattern childGuard
    simpa only [d1837, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1119 (pattern : Twelve) (guard : d1837 pattern = 1) : d1391 pattern ≤ (0 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1391, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1118 pattern childGuard
    simpa only [d1391, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1391, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1391, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
