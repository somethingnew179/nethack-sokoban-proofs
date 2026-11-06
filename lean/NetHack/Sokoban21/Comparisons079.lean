/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons078
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c11060 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d1 pattern := by
  change (0 : Int) ≤ (1 : Int) + 1
  decide
theorem c11061 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11060 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11062 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11061 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11063 (pattern : Twelve) (guard : d0 pattern = 1) : d163 pattern ≤ (1 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11064 (pattern : Twelve) (guard : d1848 pattern = 1) : d367 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d1848, d367, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11063 pattern childGuard
    simpa only [d1848, d367, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11065 (pattern : Twelve) (guard : d1901 pattern = 1) : d373 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11059 pattern childGuard
    simpa only [d1901, d373, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11064 pattern childGuard
    simpa only [d1901, d373, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11066 (pattern : Twelve) (guard : d0 pattern = 1) : d366 pattern ≤ (1 : Int) + d817 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11067 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (1 : Int) + d19 pattern := by
  omega
theorem c11068 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11069 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11067 pattern childGuard
    simpa only [d1848, d29, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11068 pattern childGuard
    simpa only [d1848, d29, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11070 (pattern : Twelve) (guard : d1901 pattern = 1) : d374 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11066 pattern childGuard
    simpa only [d1901, d374, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11069 pattern childGuard
    simpa only [d1901, d374, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11071 (pattern : Twelve) (guard : d1901 pattern = 1) : d390 pattern ≤ (1 : Int) + d1903 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d390, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11065 pattern childGuard
    simpa only [d390, d1903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d390, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11070 pattern childGuard
    simpa only [d390, d1903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11072 (pattern : Twelve) (guard : d1901 pattern = 1) : d402 pattern ≤ (1 : Int) + d1904 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d402, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11058 pattern childGuard
    simpa only [d402, d1904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d402, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11071 pattern childGuard
    simpa only [d402, d1904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11073 (pattern : Twelve) (guard : d0 pattern = 1) : d368 pattern ≤ (1 : Int) + d30 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11074 (pattern : Twelve) (guard : d0 pattern = 1) : d167 pattern ≤ (1 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11075 (pattern : Twelve) (guard : d1848 pattern = 1) : d369 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d369, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d369, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d369, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11074 pattern childGuard
    simpa only [d1848, d369, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11076 (pattern : Twelve) (guard : d1901 pattern = 1) : d375 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11073 pattern childGuard
    simpa only [d1901, d375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11075 pattern childGuard
    simpa only [d1901, d375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11077 (pattern : Twelve) (guard : d0 pattern = 1) : d369 pattern ≤ (1 : Int) + d34 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11078 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11079 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1848, d36, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11078 pattern childGuard
    simpa only [d1848, d36, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11080 (pattern : Twelve) (guard : d1901 pattern = 1) : d376 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11077 pattern childGuard
    simpa only [d1901, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11079 pattern childGuard
    simpa only [d1901, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11081 (pattern : Twelve) (guard : d1901 pattern = 1) : d391 pattern ≤ (1 : Int) + d1905 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d391, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11076 pattern childGuard
    simpa only [d391, d1905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d391, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11080 pattern childGuard
    simpa only [d391, d1905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11082 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d1848, d35, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11078 pattern childGuard
    simpa only [d1848, d35, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11083 (pattern : Twelve) (guard : d1901 pattern = 1) : d377 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11077 pattern childGuard
    simpa only [d1901, d377, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11082 pattern childGuard
    simpa only [d1901, d377, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11084 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (1 : Int) + d817 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11085 (pattern : Twelve) (guard : d1901 pattern = 1) : d378 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11084 pattern childGuard
    simpa only [d1901, d378, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11069 pattern childGuard
    simpa only [d1901, d378, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11086 (pattern : Twelve) (guard : d1901 pattern = 1) : d392 pattern ≤ (1 : Int) + d1906 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d392, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11083 pattern childGuard
    simpa only [d392, d1906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d392, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11085 pattern childGuard
    simpa only [d392, d1906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11087 (pattern : Twelve) (guard : d1901 pattern = 1) : d403 pattern ≤ (1 : Int) + d1907 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d403, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11081 pattern childGuard
    simpa only [d403, d1907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d403, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11086 pattern childGuard
    simpa only [d403, d1907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11088 (pattern : Twelve) (guard : d1901 pattern = 1) : d409 pattern ≤ (1 : Int) + d1908 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d409, d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11072 pattern childGuard
    simpa only [d409, d1908, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d409, d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11087 pattern childGuard
    simpa only [d409, d1908, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11089 (pattern : Twelve) (guard : d0 pattern = 1) : d368 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11090 (pattern : Twelve) (guard : d0 pattern = 1) : d167 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11091 (pattern : Twelve) (guard : d1848 pattern = 1) : d369 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d369, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11090 pattern childGuard
    simpa only [d1848, d369, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11092 (pattern : Twelve) (guard : d1901 pattern = 1) : d375 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11089 pattern childGuard
    simpa only [d1901, d375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11091 pattern childGuard
    simpa only [d1901, d375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11093 (pattern : Twelve) (guard : d0 pattern = 1) : d369 pattern ≤ (1 : Int) + d27 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11094 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11095 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1848, d36, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11094 pattern childGuard
    simpa only [d1848, d36, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11096 (pattern : Twelve) (guard : d1901 pattern = 1) : d376 pattern ≤ (1 : Int) + d27 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11093 pattern childGuard
    simpa only [d1901, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11095 pattern childGuard
    simpa only [d1901, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11097 (pattern : Twelve) (guard : d1901 pattern = 1) : d391 pattern ≤ (1 : Int) + d1902 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d391, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11092 pattern childGuard
    simpa only [d391, d1902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d391, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11096 pattern childGuard
    simpa only [d391, d1902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11098 (pattern : Twelve) (guard : d0 pattern = 1) : d369 pattern ≤ (1 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11099 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11100 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11099 pattern childGuard
    simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11101 (pattern : Twelve) (guard : d1901 pattern = 1) : d377 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11098 pattern childGuard
    simpa only [d1901, d377, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11100 pattern childGuard
    simpa only [d1901, d377, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11102 (pattern : Twelve) (guard : d1901 pattern = 1) : d392 pattern ≤ (1 : Int) + d1903 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d392, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11101 pattern childGuard
    simpa only [d392, d1903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d392, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11085 pattern childGuard
    simpa only [d392, d1903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11103 (pattern : Twelve) (guard : d1901 pattern = 1) : d403 pattern ≤ (1 : Int) + d1904 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d403, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11097 pattern childGuard
    simpa only [d403, d1904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d403, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11102 pattern childGuard
    simpa only [d403, d1904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11104 (pattern : Twelve) (guard : d0 pattern = 1) : d33 pattern ≤ (1 : Int) + d30 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11105 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11106 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d35, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11105 pattern childGuard
    simpa only [d1848, d35, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11107 (pattern : Twelve) (guard : d1901 pattern = 1) : d379 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11104 pattern childGuard
    simpa only [d1901, d379, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11106 pattern childGuard
    simpa only [d1901, d379, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11108 (pattern : Twelve) (guard : d0 pattern = 1) : d35 pattern ≤ (1 : Int) + d34 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11109 (pattern : Twelve) (guard : d1901 pattern = 1) : d380 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11108 pattern childGuard
    simpa only [d1901, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11079 pattern childGuard
    simpa only [d1901, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11110 (pattern : Twelve) (guard : d1901 pattern = 1) : d393 pattern ≤ (1 : Int) + d1905 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d393, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11107 pattern childGuard
    simpa only [d393, d1905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d393, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11109 pattern childGuard
    simpa only [d393, d1905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11111 (pattern : Twelve) (guard : d1901 pattern = 1) : d35 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11108 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11082 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11112 (pattern : Twelve) (guard : d1901 pattern = 1) : d394 pattern ≤ (1 : Int) + d1906 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d394, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11111 pattern childGuard
    simpa only [d394, d1906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d394, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11085 pattern childGuard
    simpa only [d394, d1906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11113 (pattern : Twelve) (guard : d1901 pattern = 1) : d404 pattern ≤ (1 : Int) + d1907 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d404, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11110 pattern childGuard
    simpa only [d404, d1907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d404, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11112 pattern childGuard
    simpa only [d404, d1907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11114 (pattern : Twelve) (guard : d1901 pattern = 1) : d410 pattern ≤ (1 : Int) + d1908 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d410, d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11103 pattern childGuard
    simpa only [d410, d1908, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d410, d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11113 pattern childGuard
    simpa only [d410, d1908, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11115 (pattern : Twelve) (guard : d1901 pattern = 1) : d415 pattern ≤ (1 : Int) + d1908 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11088 pattern childGuard
    simpa only [d415, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11114 pattern childGuard
    simpa only [d415, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11116 (pattern : Twelve) (guard : d0 pattern = 1) : d370 pattern ≤ (1 : Int) + d30 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11117 (pattern : Twelve) (guard : d0 pattern = 1) : d170 pattern ≤ (1 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11118 (pattern : Twelve) (guard : d1848 pattern = 1) : d371 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d371, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d371, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d371, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11117 pattern childGuard
    simpa only [d1848, d371, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11119 (pattern : Twelve) (guard : d1901 pattern = 1) : d381 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11116 pattern childGuard
    simpa only [d1901, d381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11118 pattern childGuard
    simpa only [d1901, d381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11120 (pattern : Twelve) (guard : d0 pattern = 1) : d371 pattern ≤ (1 : Int) + d34 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11121 (pattern : Twelve) (guard : d1901 pattern = 1) : d382 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11120 pattern childGuard
    simpa only [d1901, d382, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11079 pattern childGuard
    simpa only [d1901, d382, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11122 (pattern : Twelve) (guard : d1901 pattern = 1) : d395 pattern ≤ (1 : Int) + d1905 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d395, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11119 pattern childGuard
    simpa only [d395, d1905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d395, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11121 pattern childGuard
    simpa only [d395, d1905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11123 (pattern : Twelve) (guard : d1901 pattern = 1) : d383 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11120 pattern childGuard
    simpa only [d1901, d383, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11082 pattern childGuard
    simpa only [d1901, d383, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11124 (pattern : Twelve) (guard : d1901 pattern = 1) : d396 pattern ≤ (1 : Int) + d1906 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d396, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11123 pattern childGuard
    simpa only [d396, d1906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d396, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11085 pattern childGuard
    simpa only [d396, d1906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11125 (pattern : Twelve) (guard : d1901 pattern = 1) : d405 pattern ≤ (1 : Int) + d1907 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d405, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11122 pattern childGuard
    simpa only [d405, d1907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d405, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11124 pattern childGuard
    simpa only [d405, d1907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11126 (pattern : Twelve) (guard : d0 pattern = 1) : d39 pattern ≤ (1 : Int) + d38 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11127 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d2 pattern := by
  omega
theorem c11128 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11129 (pattern : Twelve) (guard : d1848 pattern = 1) : d39 pattern ≤ (1 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d39, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d1848, d39, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d39, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11128 pattern childGuard
    simpa only [d1848, d39, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11130 (pattern : Twelve) (guard : d1901 pattern = 1) : d39 pattern ≤ (1 : Int) + d38 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11126 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11129 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11131 (pattern : Twelve) (guard : d0 pattern = 1) : d39 pattern ≤ (1 : Int) + d41 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11132 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (1 : Int) + d23 pattern := by
  omega
theorem c11133 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d24 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11134 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (1 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d40, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11132 pattern childGuard
    simpa only [d1848, d40, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d40, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11133 pattern childGuard
    simpa only [d1848, d40, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11135 (pattern : Twelve) (guard : d1901 pattern = 1) : d384 pattern ≤ (1 : Int) + d41 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11131 pattern childGuard
    simpa only [d1901, d384, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11134 pattern childGuard
    simpa only [d1901, d384, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11136 (pattern : Twelve) (guard : d1901 pattern = 1) : d397 pattern ≤ (1 : Int) + d1909 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d397, d1909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11130 pattern childGuard
    simpa only [d397, d1909, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d397, d1909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11135 pattern childGuard
    simpa only [d397, d1909, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11137 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d3 pattern := by
  change (2 : Int) ≤ (1 : Int) + 3
  decide
theorem c11138 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11139 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11138 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11140 (pattern : Twelve) (guard : d1848 pattern = 1) : d39 pattern ≤ (1 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d39, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11139 pattern childGuard
    simpa only [d1848, d39, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d39, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11133 pattern childGuard
    simpa only [d1848, d39, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11141 (pattern : Twelve) (guard : d1901 pattern = 1) : d39 pattern ≤ (1 : Int) + d41 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11131 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11140 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11142 (pattern : Twelve) (guard : d0 pattern = 1) : d40 pattern ≤ (1 : Int) + d821 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11143 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (1 : Int) + d25 pattern := by
  omega
theorem c11144 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d21 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11145 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d42, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11143 pattern childGuard
    simpa only [d1848, d42, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d42, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11144 pattern childGuard
    simpa only [d1848, d42, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11146 (pattern : Twelve) (guard : d1901 pattern = 1) : d385 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11142 pattern childGuard
    simpa only [d1901, d385, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11145 pattern childGuard
    simpa only [d1901, d385, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11147 (pattern : Twelve) (guard : d1901 pattern = 1) : d398 pattern ≤ (1 : Int) + d1910 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d398, d1910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11141 pattern childGuard
    simpa only [d398, d1910, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d398, d1910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11146 pattern childGuard
    simpa only [d398, d1910, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11148 (pattern : Twelve) (guard : d1901 pattern = 1) : d406 pattern ≤ (1 : Int) + d1911 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d406, d1911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11136 pattern childGuard
    simpa only [d406, d1911, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d406, d1911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11147 pattern childGuard
    simpa only [d406, d1911, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11149 (pattern : Twelve) (guard : d1901 pattern = 1) : d411 pattern ≤ (1 : Int) + d1912 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d411, d1912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11125 pattern childGuard
    simpa only [d411, d1912, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d411, d1912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11148 pattern childGuard
    simpa only [d411, d1912, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11150 (pattern : Twelve) (guard : d0 pattern = 1) : d35 pattern ≤ (1 : Int) + d30 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11151 (pattern : Twelve) (guard : d1901 pattern = 1) : d35 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11150 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11106 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11152 (pattern : Twelve) (guard : d1901 pattern = 1) : d399 pattern ≤ (1 : Int) + d1905 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d399, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11151 pattern childGuard
    simpa only [d399, d1905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d399, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11109 pattern childGuard
    simpa only [d399, d1905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11153 (pattern : Twelve) (guard : d1901 pattern = 1) : d407 pattern ≤ (1 : Int) + d1907 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d407, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11152 pattern childGuard
    simpa only [d407, d1907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d407, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11112 pattern childGuard
    simpa only [d407, d1907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11154 (pattern : Twelve) (guard : d1901 pattern = 1) : d6 pattern ≤ (1 : Int) + d6 pattern := by
  omega
theorem c11155 (pattern : Twelve) (guard : d1901 pattern = 1) : d412 pattern ≤ (1 : Int) + d1913 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d412, d1913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11153 pattern childGuard
    simpa only [d412, d1913, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d412, d1913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11154 pattern childGuard
    simpa only [d412, d1913, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11156 (pattern : Twelve) (guard : d1901 pattern = 1) : d416 pattern ≤ (1 : Int) + d1914 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d416, d1914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11149 pattern childGuard
    simpa only [d416, d1914, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d416, d1914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11155 pattern childGuard
    simpa only [d416, d1914, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11157 (pattern : Twelve) (guard : d1901 pattern = 1) : d419 pattern ≤ (1 : Int) + d1915 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d419, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11115 pattern childGuard
    simpa only [d419, d1915, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d419, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11156 pattern childGuard
    simpa only [d419, d1915, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11158 (pattern : Twelve) (guard : d0 pattern = 1) : d35 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11159 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11160 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11159 pattern childGuard
    simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11161 (pattern : Twelve) (guard : d1901 pattern = 1) : d35 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11158 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11160 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11162 (pattern : Twelve) (guard : d0 pattern = 1) : d35 pattern ≤ (1 : Int) + d27 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11163 (pattern : Twelve) (guard : d1901 pattern = 1) : d380 pattern ≤ (1 : Int) + d27 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11162 pattern childGuard
    simpa only [d1901, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11095 pattern childGuard
    simpa only [d1901, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11164 (pattern : Twelve) (guard : d1901 pattern = 1) : d399 pattern ≤ (1 : Int) + d1902 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d399, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11161 pattern childGuard
    simpa only [d399, d1902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d399, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11163 pattern childGuard
    simpa only [d399, d1902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11165 (pattern : Twelve) (guard : d0 pattern = 1) : d35 pattern ≤ (1 : Int) + d823 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11166 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (1 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d1848, d35, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11105 pattern childGuard
    simpa only [d1848, d35, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11167 (pattern : Twelve) (guard : d1901 pattern = 1) : d35 pattern ≤ (1 : Int) + d823 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11165 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11166 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11168 (pattern : Twelve) (guard : d1901 pattern = 1) : d394 pattern ≤ (1 : Int) + d1916 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d394, d1916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11167 pattern childGuard
    simpa only [d394, d1916, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d394, d1916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11085 pattern childGuard
    simpa only [d394, d1916, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11169 (pattern : Twelve) (guard : d1901 pattern = 1) : d407 pattern ≤ (1 : Int) + d1917 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d407, d1917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11164 pattern childGuard
    simpa only [d407, d1917, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d407, d1917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11168 pattern childGuard
    simpa only [d407, d1917, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11170 (pattern : Twelve) (guard : d1901 pattern = 1) : d407 pattern ≤ (1 : Int) + d1918 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11169 pattern childGuard
    simpa only [d1918, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11153 pattern childGuard
    simpa only [d1918, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11171 (pattern : Twelve) (guard : d1901 pattern = 1) : d413 pattern ≤ (1 : Int) + d1912 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d413, d1912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11153 pattern childGuard
    simpa only [d413, d1912, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d413, d1912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11148 pattern childGuard
    simpa only [d413, d1912, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11172 (pattern : Twelve) (guard : d1901 pattern = 1) : d417 pattern ≤ (1 : Int) + d1914 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d417, d1914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11171 pattern childGuard
    simpa only [d417, d1914, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d417, d1914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11155 pattern childGuard
    simpa only [d417, d1914, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11173 (pattern : Twelve) (guard : d1901 pattern = 1) : d420 pattern ≤ (1 : Int) + d1919 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d420, d1919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11170 pattern childGuard
    simpa only [d420, d1919, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d420, d1919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11172 pattern childGuard
    simpa only [d420, d1919, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11174 (pattern : Twelve) (guard : d1901 pattern = 1) : d422 pattern ≤ (1 : Int) + d1920 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d422, d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11157 pattern childGuard
    simpa only [d422, d1920, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d422, d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11173 pattern childGuard
    simpa only [d422, d1920, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11175 (pattern : Twelve) (guard : d0 pattern = 1) : d35 pattern ≤ (1 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11176 (pattern : Twelve) (guard : d1901 pattern = 1) : d35 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11175 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11100 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11177 (pattern : Twelve) (guard : d1901 pattern = 1) : d394 pattern ≤ (1 : Int) + d1903 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d394, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11176 pattern childGuard
    simpa only [d394, d1903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d394, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11085 pattern childGuard
    simpa only [d394, d1903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11178 (pattern : Twelve) (guard : d1901 pattern = 1) : d407 pattern ≤ (1 : Int) + d1904 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d407, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11164 pattern childGuard
    simpa only [d407, d1904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d407, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11177 pattern childGuard
    simpa only [d407, d1904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11179 (pattern : Twelve) (guard : d1901 pattern = 1) : d407 pattern ≤ (1 : Int) + d1908 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11178 pattern childGuard
    simpa only [d1908, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11153 pattern childGuard
    simpa only [d1908, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11180 (pattern : Twelve) (guard : d1901 pattern = 1) : d420 pattern ≤ (1 : Int) + d1915 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d420, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11179 pattern childGuard
    simpa only [d420, d1915, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d420, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11172 pattern childGuard
    simpa only [d420, d1915, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11181 (pattern : Twelve) (guard : d1901 pattern = 1) : d420 pattern ≤ (1 : Int) + d1920 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11180 pattern childGuard
    simpa only [d1920, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11173 pattern childGuard
    simpa only [d1920, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11182 (pattern : Twelve) (guard : d1901 pattern = 1) : d423 pattern ≤ (1 : Int) + d1920 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11174 pattern childGuard
    simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11181 pattern childGuard
    simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11183 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (1 : Int) + d2 pattern := by
  change (3 : Int) ≤ (1 : Int) + 2
  decide
theorem c11184 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (1 : Int) + d3 pattern := by
  change (4 : Int) ≤ (1 : Int) + 3
  decide
theorem c11185 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (1 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d117, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11184 pattern childGuard
    simpa only [d117, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11186 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (1 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11185 pattern childGuard
    simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11187 (pattern : Twelve) (guard : d1848 pattern = 1) : d125 pattern ≤ (1 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d125, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11186 pattern childGuard
    simpa only [d1848, d125, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d125, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11133 pattern childGuard
    simpa only [d1848, d125, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11188 (pattern : Twelve) (guard : d1901 pattern = 1) : d386 pattern ≤ (1 : Int) + d41 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11131 pattern childGuard
    simpa only [d1901, d386, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11187 pattern childGuard
    simpa only [d1901, d386, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11189 (pattern : Twelve) (guard : d1901 pattern = 1) : d400 pattern ≤ (1 : Int) + d1909 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d400, d1909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11130 pattern childGuard
    simpa only [d400, d1909, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d400, d1909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11188 pattern childGuard
    simpa only [d400, d1909, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11190 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (1 : Int) + d3 pattern := by
  omega
theorem c11191 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (1 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11190 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11192 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (1 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11191 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11193 (pattern : Twelve) (guard : d1848 pattern = 1) : d47 pattern ≤ (1 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d47, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11192 pattern childGuard
    simpa only [d1848, d47, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d47, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11133 pattern childGuard
    simpa only [d1848, d47, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11194 (pattern : Twelve) (guard : d1901 pattern = 1) : d387 pattern ≤ (1 : Int) + d41 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11131 pattern childGuard
    simpa only [d1901, d387, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11193 pattern childGuard
    simpa only [d1901, d387, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11195 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (1 : Int) + d4 pattern := by
  change (5 : Int) ≤ (1 : Int) + 4
  decide
theorem c11196 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (1 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d12, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11195 pattern childGuard
    simpa only [d12, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11197 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (1 : Int) + d5 pattern := by
  change (6 : Int) ≤ (1 : Int) + 5
  decide
theorem c11198 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11184 pattern childGuard
    simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11197 pattern childGuard
    simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11199 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11196 pattern childGuard
    simpa only [d20, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11198 pattern childGuard
    simpa only [d20, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
