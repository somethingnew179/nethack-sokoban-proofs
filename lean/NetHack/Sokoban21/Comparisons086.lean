/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons085
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c12040 (pattern : Twelve) (guard : d0 pattern = 1) : d89 pattern ≤ (1 : Int) + d69 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12041 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (1 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11184 pattern childGuard
    simpa only [d48, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d48, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12042 (pattern : Twelve) (guard : d1 pattern = 1) : d70 pattern ≤ (1 : Int) + d69 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12003 pattern childGuard
    simpa only [d70, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12041 pattern childGuard
    simpa only [d70, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12043 (pattern : Twelve) (guard : d0 pattern = 1) : d71 pattern ≤ (1 : Int) + d69 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12044 (pattern : Twelve) (guard : d1852 pattern = 1) : d90 pattern ≤ (1 : Int) + d69 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12042 pattern childGuard
    simpa only [d1852, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12043 pattern childGuard
    simpa only [d1852, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12045 (pattern : Twelve) (guard : d1999 pattern = 1) : d101 pattern ≤ (1 : Int) + d69 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12040 pattern childGuard
    simpa only [d1999, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12044 pattern childGuard
    simpa only [d1999, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12046 (pattern : Twelve) (guard : d1999 pattern = 1) : d108 pattern ≤ (1 : Int) + d2031 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d108, d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12039 pattern childGuard
    simpa only [d108, d2031, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d108, d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12045 pattern childGuard
    simpa only [d108, d2031, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12047 (pattern : Twelve) (guard : d1999 pattern = 1) : d109 pattern ≤ (1 : Int) + d2032 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d109, d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12031 pattern childGuard
    simpa only [d109, d2032, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d109, d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11762 pattern childGuard
    simpa only [d109, d2032, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12048 (pattern : Twelve) (guard : d1999 pattern = 1) : d113 pattern ≤ (1 : Int) + d2033 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d113, d2033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12046 pattern childGuard
    simpa only [d113, d2033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d113, d2033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12047 pattern childGuard
    simpa only [d113, d2033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12049 (pattern : Twelve) (guard : d1999 pattern = 1) : d115 pattern ≤ (1 : Int) + d2034 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d115, d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12033 pattern childGuard
    simpa only [d115, d2034, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d115, d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12048 pattern childGuard
    simpa only [d115, d2034, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12050 (pattern : Twelve) (guard : d1999 pattern = 1) : d116 pattern ≤ (1 : Int) + d2035 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d116, d2035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12012 pattern childGuard
    simpa only [d116, d2035, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d116, d2035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12049 pattern childGuard
    simpa only [d116, d2035, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12051 (pattern : Twelve) (guard : d0 pattern = 1) : d838 pattern ≤ (1 : Int) + d824 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12052 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11060 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11212 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12053 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11060 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12052 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12054 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12053 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12055 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11061 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12052 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12056 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12055 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12053 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12057 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12054 pattern childGuard
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12056 pattern childGuard
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12058 (pattern : Twelve) (guard : d0 pattern = 1) : d825 pattern ≤ (1 : Int) + d824 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12059 (pattern : Twelve) (guard : d1852 pattern = 1) : d839 pattern ≤ (1 : Int) + d824 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12057 pattern childGuard
    simpa only [d1852, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12058 pattern childGuard
    simpa only [d1852, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12060 (pattern : Twelve) (guard : d1999 pattern = 1) : d853 pattern ≤ (1 : Int) + d824 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12051 pattern childGuard
    simpa only [d1999, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12059 pattern childGuard
    simpa only [d1999, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12061 (pattern : Twelve) (guard : d0 pattern = 1) : d840 pattern ≤ (1 : Int) + d826 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12062 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (1 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12055 pattern childGuard
    simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12063 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (1 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11859 pattern childGuard
    simpa only [d827, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12062 pattern childGuard
    simpa only [d827, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12064 (pattern : Twelve) (guard : d0 pattern = 1) : d825 pattern ≤ (1 : Int) + d826 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12065 (pattern : Twelve) (guard : d1852 pattern = 1) : d841 pattern ≤ (1 : Int) + d826 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12063 pattern childGuard
    simpa only [d1852, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12064 pattern childGuard
    simpa only [d1852, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12066 (pattern : Twelve) (guard : d1999 pattern = 1) : d854 pattern ≤ (1 : Int) + d826 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12061 pattern childGuard
    simpa only [d1999, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12065 pattern childGuard
    simpa only [d1999, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12067 (pattern : Twelve) (guard : d1999 pattern = 1) : d861 pattern ≤ (1 : Int) + d2036 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d861, d2036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12060 pattern childGuard
    simpa only [d861, d2036, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d861, d2036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12066 pattern childGuard
    simpa only [d861, d2036, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12068 (pattern : Twelve) (guard : d0 pattern = 1) : d842 pattern ≤ (1 : Int) + d828 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12069 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11190 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12070 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12069 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12071 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (1 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12055 pattern childGuard
    simpa only [d34, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12070 pattern childGuard
    simpa only [d34, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12072 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (1 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11859 pattern childGuard
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12071 pattern childGuard
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12073 (pattern : Twelve) (guard : d0 pattern = 1) : d825 pattern ≤ (1 : Int) + d828 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12074 (pattern : Twelve) (guard : d1852 pattern = 1) : d843 pattern ≤ (1 : Int) + d828 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12072 pattern childGuard
    simpa only [d1852, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12073 pattern childGuard
    simpa only [d1852, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12075 (pattern : Twelve) (guard : d1999 pattern = 1) : d855 pattern ≤ (1 : Int) + d828 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12068 pattern childGuard
    simpa only [d1999, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12074 pattern childGuard
    simpa only [d1999, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12076 (pattern : Twelve) (guard : d0 pattern = 1) : d844 pattern ≤ (1 : Int) + d829 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12077 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (1 : Int) + d41 pattern := by
  omega
theorem c12078 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (1 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11138 pattern childGuard
    simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12069 pattern childGuard
    simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12079 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (1 : Int) + d820 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12078 pattern childGuard
    simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12080 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (1 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12077 pattern childGuard
    simpa only [d830, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12079 pattern childGuard
    simpa only [d830, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12081 (pattern : Twelve) (guard : d0 pattern = 1) : d831 pattern ≤ (1 : Int) + d829 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12082 (pattern : Twelve) (guard : d1852 pattern = 1) : d845 pattern ≤ (1 : Int) + d829 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12080 pattern childGuard
    simpa only [d1852, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12081 pattern childGuard
    simpa only [d1852, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12083 (pattern : Twelve) (guard : d1999 pattern = 1) : d856 pattern ≤ (1 : Int) + d829 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12076 pattern childGuard
    simpa only [d1999, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12082 pattern childGuard
    simpa only [d1999, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12084 (pattern : Twelve) (guard : d1999 pattern = 1) : d862 pattern ≤ (1 : Int) + d2037 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d862, d2037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12075 pattern childGuard
    simpa only [d862, d2037, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d862, d2037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12083 pattern childGuard
    simpa only [d862, d2037, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12085 (pattern : Twelve) (guard : d1999 pattern = 1) : d863 pattern ≤ (1 : Int) + d2038 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d863, d2038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12066 pattern childGuard
    simpa only [d863, d2038, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d863, d2038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11762 pattern childGuard
    simpa only [d863, d2038, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12086 (pattern : Twelve) (guard : d1999 pattern = 1) : d867 pattern ≤ (1 : Int) + d2039 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d867, d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12084 pattern childGuard
    simpa only [d867, d2039, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d867, d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12085 pattern childGuard
    simpa only [d867, d2039, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12087 (pattern : Twelve) (guard : d1999 pattern = 1) : d869 pattern ≤ (1 : Int) + d2040 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d869, d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12067 pattern childGuard
    simpa only [d869, d2040, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d869, d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12086 pattern childGuard
    simpa only [d869, d2040, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12088 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (1 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d823, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12013 pattern childGuard
    simpa only [d823, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12089 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (1 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12055 pattern childGuard
    simpa only [d823, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12013 pattern childGuard
    simpa only [d823, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12090 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (1 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12088 pattern childGuard
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12089 pattern childGuard
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12091 (pattern : Twelve) (guard : d1852 pattern = 1) : d846 pattern ≤ (1 : Int) + d824 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12090 pattern childGuard
    simpa only [d1852, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12058 pattern childGuard
    simpa only [d1852, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12092 (pattern : Twelve) (guard : d1999 pattern = 1) : d857 pattern ≤ (1 : Int) + d824 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12051 pattern childGuard
    simpa only [d1999, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12091 pattern childGuard
    simpa only [d1999, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12093 (pattern : Twelve) (guard : d0 pattern = 1) : d847 pattern ≤ (1 : Int) + d832 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12094 (pattern : Twelve) (guard : d1 pattern = 1) : d833 pattern ≤ (1 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11859 pattern childGuard
    simpa only [d833, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12027 pattern childGuard
    simpa only [d833, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12095 (pattern : Twelve) (guard : d0 pattern = 1) : d825 pattern ≤ (1 : Int) + d832 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12096 (pattern : Twelve) (guard : d1852 pattern = 1) : d848 pattern ≤ (1 : Int) + d832 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12094 pattern childGuard
    simpa only [d1852, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12095 pattern childGuard
    simpa only [d1852, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12097 (pattern : Twelve) (guard : d1999 pattern = 1) : d858 pattern ≤ (1 : Int) + d832 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12093 pattern childGuard
    simpa only [d1999, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12096 pattern childGuard
    simpa only [d1999, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12098 (pattern : Twelve) (guard : d1999 pattern = 1) : d864 pattern ≤ (1 : Int) + d2041 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d864, d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12092 pattern childGuard
    simpa only [d864, d2041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d864, d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12097 pattern childGuard
    simpa only [d864, d2041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12099 (pattern : Twelve) (guard : d0 pattern = 1) : d849 pattern ≤ (1 : Int) + d834 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12100 (pattern : Twelve) (guard : d1 pattern = 1) : d835 pattern ≤ (1 : Int) + d834 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11859 pattern childGuard
    simpa only [d835, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12035 pattern childGuard
    simpa only [d835, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12101 (pattern : Twelve) (guard : d0 pattern = 1) : d825 pattern ≤ (1 : Int) + d834 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12102 (pattern : Twelve) (guard : d1852 pattern = 1) : d850 pattern ≤ (1 : Int) + d834 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12100 pattern childGuard
    simpa only [d1852, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12101 pattern childGuard
    simpa only [d1852, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12103 (pattern : Twelve) (guard : d1999 pattern = 1) : d859 pattern ≤ (1 : Int) + d834 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12099 pattern childGuard
    simpa only [d1999, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12102 pattern childGuard
    simpa only [d1999, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12104 (pattern : Twelve) (guard : d0 pattern = 1) : d851 pattern ≤ (1 : Int) + d836 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12105 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (1 : Int) + d836 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12077 pattern childGuard
    simpa only [d837, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12041 pattern childGuard
    simpa only [d837, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12106 (pattern : Twelve) (guard : d0 pattern = 1) : d831 pattern ≤ (1 : Int) + d836 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12107 (pattern : Twelve) (guard : d1852 pattern = 1) : d852 pattern ≤ (1 : Int) + d836 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12105 pattern childGuard
    simpa only [d1852, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12106 pattern childGuard
    simpa only [d1852, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12108 (pattern : Twelve) (guard : d1999 pattern = 1) : d860 pattern ≤ (1 : Int) + d836 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12104 pattern childGuard
    simpa only [d1999, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12107 pattern childGuard
    simpa only [d1999, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12109 (pattern : Twelve) (guard : d1999 pattern = 1) : d865 pattern ≤ (1 : Int) + d2042 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d865, d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12103 pattern childGuard
    simpa only [d865, d2042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d865, d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12108 pattern childGuard
    simpa only [d865, d2042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12110 (pattern : Twelve) (guard : d1999 pattern = 1) : d866 pattern ≤ (1 : Int) + d2043 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d866, d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12097 pattern childGuard
    simpa only [d866, d2043, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d866, d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11762 pattern childGuard
    simpa only [d866, d2043, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12111 (pattern : Twelve) (guard : d1999 pattern = 1) : d868 pattern ≤ (1 : Int) + d2044 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d868, d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12109 pattern childGuard
    simpa only [d868, d2044, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d868, d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12110 pattern childGuard
    simpa only [d868, d2044, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12112 (pattern : Twelve) (guard : d1999 pattern = 1) : d870 pattern ≤ (1 : Int) + d2045 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d870, d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12098 pattern childGuard
    simpa only [d870, d2045, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d870, d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12111 pattern childGuard
    simpa only [d870, d2045, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12113 (pattern : Twelve) (guard : d1999 pattern = 1) : d871 pattern ≤ (1 : Int) + d2046 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d871, d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12087 pattern childGuard
    simpa only [d871, d2046, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d871, d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12112 pattern childGuard
    simpa only [d871, d2046, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12114 (pattern : Twelve) (guard : d0 pattern = 1) : d1293 pattern ≤ (1 : Int) + d1284 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12115 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (1 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d10, d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12013 pattern childGuard
    simpa only [d10, d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12116 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (1 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11212 pattern childGuard
    simpa only [d11, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d11, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12117 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (1 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12115 pattern childGuard
    simpa only [d19, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12116 pattern childGuard
    simpa only [d19, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12118 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11060 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12013 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12119 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (1 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12118 pattern childGuard
    simpa only [d19, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12116 pattern childGuard
    simpa only [d19, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12120 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (1 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12117 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12119 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12121 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (1 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12120 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12119 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12122 (pattern : Twelve) (guard : d1852 pattern = 1) : d1294 pattern ≤ (1 : Int) + d1284 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12121 pattern childGuard
    simpa only [d1852, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11851 pattern childGuard
    simpa only [d1852, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12123 (pattern : Twelve) (guard : d1999 pattern = 1) : d1305 pattern ≤ (1 : Int) + d1284 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12114 pattern childGuard
    simpa only [d1999, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12122 pattern childGuard
    simpa only [d1999, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12124 (pattern : Twelve) (guard : d0 pattern = 1) : d1295 pattern ≤ (1 : Int) + d1285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12125 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (1 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d16, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11184 pattern childGuard
    simpa only [d16, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12126 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (1 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11190 pattern childGuard
    simpa only [d12, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11195 pattern childGuard
    simpa only [d12, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12127 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (1 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12125 pattern childGuard
    simpa only [d25, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12126 pattern childGuard
    simpa only [d25, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12128 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (1 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12117 pattern childGuard
    simpa only [d817, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12127 pattern childGuard
    simpa only [d817, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12129 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (1 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12119 pattern childGuard
    simpa only [d29, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d29, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12130 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (1 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12128 pattern childGuard
    simpa only [d1286, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12129 pattern childGuard
    simpa only [d1286, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12131 (pattern : Twelve) (guard : d1852 pattern = 1) : d1296 pattern ≤ (1 : Int) + d1285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12130 pattern childGuard
    simpa only [d1852, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11846 pattern childGuard
    simpa only [d1852, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12132 (pattern : Twelve) (guard : d1999 pattern = 1) : d1306 pattern ≤ (1 : Int) + d1285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12124 pattern childGuard
    simpa only [d1999, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12131 pattern childGuard
    simpa only [d1999, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12133 (pattern : Twelve) (guard : d1999 pattern = 1) : d1313 pattern ≤ (1 : Int) + d2047 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1313, d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12123 pattern childGuard
    simpa only [d1313, d2047, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1313, d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12132 pattern childGuard
    simpa only [d1313, d2047, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12134 (pattern : Twelve) (guard : d0 pattern = 1) : d1297 pattern ≤ (1 : Int) + d1287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12135 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11184 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12136 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (1 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12135 pattern childGuard
    simpa only [d25, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12126 pattern childGuard
    simpa only [d25, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12137 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (1 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12119 pattern childGuard
    simpa only [d817, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12136 pattern childGuard
    simpa only [d817, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12138 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (1 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12128 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12137 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12139 (pattern : Twelve) (guard : d1852 pattern = 1) : d1298 pattern ≤ (1 : Int) + d1287 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12138 pattern childGuard
    simpa only [d1852, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11860 pattern childGuard
    simpa only [d1852, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12140 (pattern : Twelve) (guard : d1999 pattern = 1) : d1307 pattern ≤ (1 : Int) + d1287 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12134 pattern childGuard
    simpa only [d1999, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12139 pattern childGuard
    simpa only [d1999, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12141 (pattern : Twelve) (guard : d0 pattern = 1) : d1299 pattern ≤ (1 : Int) + d1288 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12142 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (1 : Int) + d4 pattern := by
  omega
theorem c12143 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (1 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12142 pattern childGuard
    simpa only [d13, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11197 pattern childGuard
    simpa only [d13, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12144 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (1 : Int) + d14 pattern := by
  omega
theorem c12145 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (1 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12143 pattern childGuard
    simpa only [d21, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12144 pattern childGuard
    simpa only [d21, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12146 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (1 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12127 pattern childGuard
    simpa only [d821, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12145 pattern childGuard
    simpa only [d821, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12147 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (1 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12136 pattern childGuard
    simpa only [d42, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d42, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12148 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (1 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12146 pattern childGuard
    simpa only [d1289, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12147 pattern childGuard
    simpa only [d1289, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12149 (pattern : Twelve) (guard : d1852 pattern = 1) : d1300 pattern ≤ (1 : Int) + d1288 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12148 pattern childGuard
    simpa only [d1852, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11865 pattern childGuard
    simpa only [d1852, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12150 (pattern : Twelve) (guard : d1999 pattern = 1) : d1308 pattern ≤ (1 : Int) + d1288 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12141 pattern childGuard
    simpa only [d1999, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12149 pattern childGuard
    simpa only [d1999, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12151 (pattern : Twelve) (guard : d1999 pattern = 1) : d1314 pattern ≤ (1 : Int) + d2048 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1314, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12140 pattern childGuard
    simpa only [d1314, d2048, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1314, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12150 pattern childGuard
    simpa only [d1314, d2048, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12152 (pattern : Twelve) (guard : d1999 pattern = 1) : d1315 pattern ≤ (1 : Int) + d2049 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1315, d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12132 pattern childGuard
    simpa only [d1315, d2049, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1315, d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11762 pattern childGuard
    simpa only [d1315, d2049, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12153 (pattern : Twelve) (guard : d1999 pattern = 1) : d1319 pattern ≤ (1 : Int) + d2050 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1319, d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12151 pattern childGuard
    simpa only [d1319, d2050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1319, d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12152 pattern childGuard
    simpa only [d1319, d2050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12154 (pattern : Twelve) (guard : d1999 pattern = 1) : d1321 pattern ≤ (1 : Int) + d2051 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1321, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12133 pattern childGuard
    simpa only [d1321, d2051, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1321, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12153 pattern childGuard
    simpa only [d1321, d2051, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12155 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (1 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12013 pattern childGuard
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12156 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (1 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12013 pattern childGuard
    simpa only [d23, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12155 pattern childGuard
    simpa only [d23, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12157 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (1 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12117 pattern childGuard
    simpa only [d1283, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12156 pattern childGuard
    simpa only [d1283, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12158 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (1 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12119 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12156 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12159 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (1 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12157 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12158 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12160 (pattern : Twelve) (guard : d1852 pattern = 1) : d1301 pattern ≤ (1 : Int) + d1284 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12159 pattern childGuard
    simpa only [d1852, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11851 pattern childGuard
    simpa only [d1852, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12161 (pattern : Twelve) (guard : d1999 pattern = 1) : d1309 pattern ≤ (1 : Int) + d1284 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12114 pattern childGuard
    simpa only [d1999, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12160 pattern childGuard
    simpa only [d1999, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12162 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (1 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12156 pattern childGuard
    simpa only [d40, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d40, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12163 (pattern : Twelve) (guard : d1 pattern = 1) : d1290 pattern ≤ (1 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12128 pattern childGuard
    simpa only [d1290, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12162 pattern childGuard
    simpa only [d1290, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12164 (pattern : Twelve) (guard : d1852 pattern = 1) : d1302 pattern ≤ (1 : Int) + d1285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12163 pattern childGuard
    simpa only [d1852, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11846 pattern childGuard
    simpa only [d1852, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12165 (pattern : Twelve) (guard : d1999 pattern = 1) : d1310 pattern ≤ (1 : Int) + d1285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12124 pattern childGuard
    simpa only [d1999, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12164 pattern childGuard
    simpa only [d1999, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12166 (pattern : Twelve) (guard : d1999 pattern = 1) : d1316 pattern ≤ (1 : Int) + d2047 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1316, d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12161 pattern childGuard
    simpa only [d1316, d2047, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1316, d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12165 pattern childGuard
    simpa only [d1316, d2047, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12167 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (1 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11184 pattern childGuard
    simpa only [d24, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11310 pattern childGuard
    simpa only [d24, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12168 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (1 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12156 pattern childGuard
    simpa only [d41, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12167 pattern childGuard
    simpa only [d41, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12169 (pattern : Twelve) (guard : d1 pattern = 1) : d1291 pattern ≤ (1 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12128 pattern childGuard
    simpa only [d1291, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12168 pattern childGuard
    simpa only [d1291, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12170 (pattern : Twelve) (guard : d1852 pattern = 1) : d1303 pattern ≤ (1 : Int) + d1287 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12169 pattern childGuard
    simpa only [d1852, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11860 pattern childGuard
    simpa only [d1852, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12171 (pattern : Twelve) (guard : d1999 pattern = 1) : d1311 pattern ≤ (1 : Int) + d1287 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12134 pattern childGuard
    simpa only [d1999, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12170 pattern childGuard
    simpa only [d1999, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12172 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (1 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12167 pattern childGuard
    simpa only [d49, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d49, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12173 (pattern : Twelve) (guard : d1 pattern = 1) : d1292 pattern ≤ (1 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12146 pattern childGuard
    simpa only [d1292, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12172 pattern childGuard
    simpa only [d1292, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12174 (pattern : Twelve) (guard : d1852 pattern = 1) : d1304 pattern ≤ (1 : Int) + d1288 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12173 pattern childGuard
    simpa only [d1852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11865 pattern childGuard
    simpa only [d1852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12175 (pattern : Twelve) (guard : d1999 pattern = 1) : d1312 pattern ≤ (1 : Int) + d1288 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12141 pattern childGuard
    simpa only [d1999, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12174 pattern childGuard
    simpa only [d1999, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12176 (pattern : Twelve) (guard : d1999 pattern = 1) : d1317 pattern ≤ (1 : Int) + d2048 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1317, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12171 pattern childGuard
    simpa only [d1317, d2048, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1317, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12175 pattern childGuard
    simpa only [d1317, d2048, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12177 (pattern : Twelve) (guard : d1999 pattern = 1) : d1318 pattern ≤ (1 : Int) + d2049 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1318, d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12165 pattern childGuard
    simpa only [d1318, d2049, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1318, d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11762 pattern childGuard
    simpa only [d1318, d2049, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12178 (pattern : Twelve) (guard : d1999 pattern = 1) : d1320 pattern ≤ (1 : Int) + d2050 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1320, d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12176 pattern childGuard
    simpa only [d1320, d2050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1320, d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12177 pattern childGuard
    simpa only [d1320, d2050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12179 (pattern : Twelve) (guard : d1999 pattern = 1) : d1322 pattern ≤ (1 : Int) + d2051 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1322, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12166 pattern childGuard
    simpa only [d1322, d2051, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1322, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12178 pattern childGuard
    simpa only [d1322, d2051, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
