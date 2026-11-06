/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons101
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c14280 (pattern : Twelve) (guard : d2301 pattern = 1) : d152 pattern ≤ (2 : Int) + d2307 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d152, d2307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14253 pattern childGuard
    simpa only [d152, d2307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d152, d2307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d152, d2307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14281 (pattern : Twelve) (guard : d2301 pattern = 1) : d154 pattern ≤ (2 : Int) + d2314 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d154, d2314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14279 pattern childGuard
    simpa only [d154, d2314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d154, d2314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14280 pattern childGuard
    simpa only [d154, d2314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14282 (pattern : Twelve) (guard : d2301 pattern = 1) : d155 pattern ≤ (2 : Int) + d2315 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d155, d2315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14255 pattern childGuard
    simpa only [d155, d2315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d155, d2315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14281 pattern childGuard
    simpa only [d155, d2315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14283 (pattern : Twelve) (guard : d2301 pattern = 1) : d156 pattern ≤ (2 : Int) + d2316 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d156, d2316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14241 pattern childGuard
    simpa only [d156, d2316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d156, d2316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14282 pattern childGuard
    simpa only [d156, d2316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14284 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (2 : Int) + d814 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14285 (pattern : Twelve) (guard : d26 pattern = 1) : d27 pattern ≤ (2 : Int) + d814 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14284 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13384 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14286 (pattern : Twelve) (guard : d0 pattern = 1) : d816 pattern ≤ (2 : Int) + d814 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14287 (pattern : Twelve) (guard : d2301 pattern = 1) : d824 pattern ≤ (2 : Int) + d814 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14285 pattern childGuard
    simpa only [d2301, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14286 pattern childGuard
    simpa only [d2301, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14288 (pattern : Twelve) (guard : d2301 pattern = 1) : d838 pattern ≤ (2 : Int) + d2317 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d838, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14168 pattern childGuard
    simpa only [d838, d2317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d838, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14287 pattern childGuard
    simpa only [d838, d2317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14289 (pattern : Twelve) (guard : d2301 pattern = 1) : d17 pattern ≤ (2 : Int) + d17 pattern := by
  omega
theorem c14290 (pattern : Twelve) (guard : d0 pattern = 1) : d19 pattern ≤ (2 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14291 (pattern : Twelve) (guard : d26 pattern = 1) : d817 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14290 pattern childGuard
    simpa only [d26, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13458 pattern childGuard
    simpa only [d26, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14292 (pattern : Twelve) (guard : d2301 pattern = 1) : d825 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14291 pattern childGuard
    simpa only [d2301, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14233 pattern childGuard
    simpa only [d2301, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14293 (pattern : Twelve) (guard : d2301 pattern = 1) : d839 pattern ≤ (2 : Int) + d1960 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d839, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14289 pattern childGuard
    simpa only [d839, d1960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d839, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14292 pattern childGuard
    simpa only [d839, d1960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14294 (pattern : Twelve) (guard : d2301 pattern = 1) : d853 pattern ≤ (2 : Int) + d2318 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d853, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14288 pattern childGuard
    simpa only [d853, d2318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d853, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14293 pattern childGuard
    simpa only [d853, d2318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14295 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (2 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13392 pattern childGuard
    simpa only [d23, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13353 pattern childGuard
    simpa only [d23, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14296 (pattern : Twelve) (guard : d26 pattern = 1) : d34 pattern ≤ (2 : Int) + d814 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14284 pattern childGuard
    simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14295 pattern childGuard
    simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14297 (pattern : Twelve) (guard : d0 pattern = 1) : d818 pattern ≤ (2 : Int) + d814 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14298 (pattern : Twelve) (guard : d2301 pattern = 1) : d826 pattern ≤ (2 : Int) + d814 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14296 pattern childGuard
    simpa only [d2301, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14297 pattern childGuard
    simpa only [d2301, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14299 (pattern : Twelve) (guard : d2301 pattern = 1) : d840 pattern ≤ (2 : Int) + d2317 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d840, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14200 pattern childGuard
    simpa only [d840, d2317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d840, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14298 pattern childGuard
    simpa only [d840, d2317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14300 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (2 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14301 (pattern : Twelve) (guard : d26 pattern = 1) : d34 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14300 pattern childGuard
    simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13299 pattern childGuard
    simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14302 (pattern : Twelve) (guard : d2301 pattern = 1) : d827 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14301 pattern childGuard
    simpa only [d2301, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14201 pattern childGuard
    simpa only [d2301, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14303 (pattern : Twelve) (guard : d2301 pattern = 1) : d841 pattern ≤ (2 : Int) + d1960 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d841, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14302 pattern childGuard
    simpa only [d841, d1960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d841, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14292 pattern childGuard
    simpa only [d841, d1960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14304 (pattern : Twelve) (guard : d2301 pattern = 1) : d854 pattern ≤ (2 : Int) + d2318 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d854, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14299 pattern childGuard
    simpa only [d854, d2318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d854, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14303 pattern childGuard
    simpa only [d854, d2318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14305 (pattern : Twelve) (guard : d2301 pattern = 1) : d861 pattern ≤ (2 : Int) + d2318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14294 pattern childGuard
    simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14304 pattern childGuard
    simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14306 (pattern : Twelve) (guard : d0 pattern = 1) : d819 pattern ≤ (2 : Int) + d814 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14307 (pattern : Twelve) (guard : d2301 pattern = 1) : d828 pattern ≤ (2 : Int) + d814 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14296 pattern childGuard
    simpa only [d2301, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14306 pattern childGuard
    simpa only [d2301, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14308 (pattern : Twelve) (guard : d2301 pattern = 1) : d842 pattern ≤ (2 : Int) + d2317 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d842, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14209 pattern childGuard
    simpa only [d842, d2317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d842, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14307 pattern childGuard
    simpa only [d842, d2317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14309 (pattern : Twelve) (guard : d0 pattern = 1) : d34 pattern ≤ (2 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14310 (pattern : Twelve) (guard : d2301 pattern = 1) : d34 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14301 pattern childGuard
    simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14309 pattern childGuard
    simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14311 (pattern : Twelve) (guard : d2301 pattern = 1) : d843 pattern ≤ (2 : Int) + d1960 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d843, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14310 pattern childGuard
    simpa only [d843, d1960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d843, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14292 pattern childGuard
    simpa only [d843, d1960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14312 (pattern : Twelve) (guard : d2301 pattern = 1) : d855 pattern ≤ (2 : Int) + d2318 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d855, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14308 pattern childGuard
    simpa only [d855, d2318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d855, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14311 pattern childGuard
    simpa only [d855, d2318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14313 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (2 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14314 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (2 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14219 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13303 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14315 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (2 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14220 pattern childGuard
    simpa only [d24, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14314 pattern childGuard
    simpa only [d24, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14316 (pattern : Twelve) (guard : d26 pattern = 1) : d41 pattern ≤ (2 : Int) + d815 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14313 pattern childGuard
    simpa only [d26, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14315 pattern childGuard
    simpa only [d26, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14317 (pattern : Twelve) (guard : d0 pattern = 1) : d820 pattern ≤ (2 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14318 (pattern : Twelve) (guard : d2301 pattern = 1) : d829 pattern ≤ (2 : Int) + d815 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14316 pattern childGuard
    simpa only [d2301, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14317 pattern childGuard
    simpa only [d2301, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14319 (pattern : Twelve) (guard : d2301 pattern = 1) : d844 pattern ≤ (2 : Int) + d2319 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d844, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14217 pattern childGuard
    simpa only [d844, d2319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d844, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14318 pattern childGuard
    simpa only [d844, d2319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14320 (pattern : Twelve) (guard : d26 pattern = 1) : d41 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13940 pattern childGuard
    simpa only [d26, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13305 pattern childGuard
    simpa only [d26, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14321 (pattern : Twelve) (guard : d2301 pattern = 1) : d830 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14320 pattern childGuard
    simpa only [d2301, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14223 pattern childGuard
    simpa only [d2301, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14322 (pattern : Twelve) (guard : d0 pattern = 1) : d25 pattern ≤ (2 : Int) + d21 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14323 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (2 : Int) + d21 pattern := by
  omega
theorem c14324 (pattern : Twelve) (guard : d26 pattern = 1) : d821 pattern ≤ (2 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14322 pattern childGuard
    simpa only [d26, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14323 pattern childGuard
    simpa only [d26, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14325 (pattern : Twelve) (guard : d0 pattern = 1) : d822 pattern ≤ (2 : Int) + d21 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14326 (pattern : Twelve) (guard : d2301 pattern = 1) : d831 pattern ≤ (2 : Int) + d21 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14324 pattern childGuard
    simpa only [d2301, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14325 pattern childGuard
    simpa only [d2301, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14327 (pattern : Twelve) (guard : d2301 pattern = 1) : d845 pattern ≤ (2 : Int) + d2320 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d845, d2320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14321 pattern childGuard
    simpa only [d845, d2320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d845, d2320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14326 pattern childGuard
    simpa only [d845, d2320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14328 (pattern : Twelve) (guard : d2301 pattern = 1) : d856 pattern ≤ (2 : Int) + d2321 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d856, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14319 pattern childGuard
    simpa only [d856, d2321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d856, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14327 pattern childGuard
    simpa only [d856, d2321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14329 (pattern : Twelve) (guard : d2301 pattern = 1) : d862 pattern ≤ (2 : Int) + d2322 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d862, d2322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14312 pattern childGuard
    simpa only [d862, d2322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d862, d2322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14328 pattern childGuard
    simpa only [d862, d2322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14330 (pattern : Twelve) (guard : d2301 pattern = 1) : d863 pattern ≤ (2 : Int) + d2323 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d863, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14304 pattern childGuard
    simpa only [d863, d2323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d863, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d863, d2323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14331 (pattern : Twelve) (guard : d2301 pattern = 1) : d867 pattern ≤ (2 : Int) + d2324 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d867, d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14329 pattern childGuard
    simpa only [d867, d2324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d867, d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14330 pattern childGuard
    simpa only [d867, d2324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14332 (pattern : Twelve) (guard : d2301 pattern = 1) : d869 pattern ≤ (2 : Int) + d2325 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d869, d2325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14305 pattern childGuard
    simpa only [d869, d2325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d869, d2325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14331 pattern childGuard
    simpa only [d869, d2325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14333 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13320 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13283 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14334 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (2 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13321 pattern childGuard
    simpa only [d872, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14333 pattern childGuard
    simpa only [d872, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14335 (pattern : Twelve) (guard : d26 pattern = 1) : d874 pattern ≤ (2 : Int) + d814 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14284 pattern childGuard
    simpa only [d26, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14334 pattern childGuard
    simpa only [d26, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14336 (pattern : Twelve) (guard : d0 pattern = 1) : d875 pattern ≤ (2 : Int) + d814 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14337 (pattern : Twelve) (guard : d2301 pattern = 1) : d882 pattern ≤ (2 : Int) + d814 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14335 pattern childGuard
    simpa only [d2301, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14336 pattern childGuard
    simpa only [d2301, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14338 (pattern : Twelve) (guard : d2301 pattern = 1) : d890 pattern ≤ (2 : Int) + d2317 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d890, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14168 pattern childGuard
    simpa only [d890, d2317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d890, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14337 pattern childGuard
    simpa only [d890, d2317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14339 (pattern : Twelve) (guard : d26 pattern = 1) : d876 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14290 pattern childGuard
    simpa only [d26, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13373 pattern childGuard
    simpa only [d26, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14340 (pattern : Twelve) (guard : d2301 pattern = 1) : d883 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14339 pattern childGuard
    simpa only [d2301, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14233 pattern childGuard
    simpa only [d2301, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14341 (pattern : Twelve) (guard : d2301 pattern = 1) : d891 pattern ≤ (2 : Int) + d1960 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d891, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14289 pattern childGuard
    simpa only [d891, d1960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d891, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14340 pattern childGuard
    simpa only [d891, d1960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14342 (pattern : Twelve) (guard : d2301 pattern = 1) : d898 pattern ≤ (2 : Int) + d2318 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d898, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14338 pattern childGuard
    simpa only [d898, d2318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d898, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14341 pattern childGuard
    simpa only [d898, d2318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14343 (pattern : Twelve) (guard : d26 pattern = 1) : d877 pattern ≤ (2 : Int) + d814 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14284 pattern childGuard
    simpa only [d26, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13364 pattern childGuard
    simpa only [d26, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14344 (pattern : Twelve) (guard : d2301 pattern = 1) : d884 pattern ≤ (2 : Int) + d814 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14343 pattern childGuard
    simpa only [d2301, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14297 pattern childGuard
    simpa only [d2301, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14345 (pattern : Twelve) (guard : d2301 pattern = 1) : d892 pattern ≤ (2 : Int) + d2317 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d892, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14200 pattern childGuard
    simpa only [d892, d2317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d892, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14344 pattern childGuard
    simpa only [d892, d2317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14346 (pattern : Twelve) (guard : d2301 pattern = 1) : d893 pattern ≤ (2 : Int) + d1960 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d893, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14302 pattern childGuard
    simpa only [d893, d1960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d893, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14340 pattern childGuard
    simpa only [d893, d1960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14347 (pattern : Twelve) (guard : d2301 pattern = 1) : d899 pattern ≤ (2 : Int) + d2318 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d899, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14345 pattern childGuard
    simpa only [d899, d2318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d899, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14346 pattern childGuard
    simpa only [d899, d2318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14348 (pattern : Twelve) (guard : d2301 pattern = 1) : d902 pattern ≤ (2 : Int) + d2318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14342 pattern childGuard
    simpa only [d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14347 pattern childGuard
    simpa only [d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14349 (pattern : Twelve) (guard : d0 pattern = 1) : d878 pattern ≤ (2 : Int) + d814 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14350 (pattern : Twelve) (guard : d2301 pattern = 1) : d885 pattern ≤ (2 : Int) + d814 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14343 pattern childGuard
    simpa only [d2301, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14349 pattern childGuard
    simpa only [d2301, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14351 (pattern : Twelve) (guard : d2301 pattern = 1) : d894 pattern ≤ (2 : Int) + d2317 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d894, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14209 pattern childGuard
    simpa only [d894, d2317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d894, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14350 pattern childGuard
    simpa only [d894, d2317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14352 (pattern : Twelve) (guard : d0 pattern = 1) : d879 pattern ≤ (2 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14353 (pattern : Twelve) (guard : d2301 pattern = 1) : d886 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14301 pattern childGuard
    simpa only [d2301, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14352 pattern childGuard
    simpa only [d2301, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14354 (pattern : Twelve) (guard : d2301 pattern = 1) : d895 pattern ≤ (2 : Int) + d1960 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d895, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14353 pattern childGuard
    simpa only [d895, d1960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d895, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14340 pattern childGuard
    simpa only [d895, d1960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14355 (pattern : Twelve) (guard : d2301 pattern = 1) : d900 pattern ≤ (2 : Int) + d2318 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d900, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14351 pattern childGuard
    simpa only [d900, d2318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d900, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14354 pattern childGuard
    simpa only [d900, d2318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14356 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (2 : Int) + d873 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14357 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13369 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13371 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14358 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (2 : Int) + d873 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13423 pattern childGuard
    simpa only [d22, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14357 pattern childGuard
    simpa only [d22, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14359 (pattern : Twelve) (guard : d26 pattern = 1) : d127 pattern ≤ (2 : Int) + d873 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14356 pattern childGuard
    simpa only [d26, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14358 pattern childGuard
    simpa only [d26, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14360 (pattern : Twelve) (guard : d0 pattern = 1) : d880 pattern ≤ (2 : Int) + d873 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14361 (pattern : Twelve) (guard : d2301 pattern = 1) : d887 pattern ≤ (2 : Int) + d873 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14359 pattern childGuard
    simpa only [d2301, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14360 pattern childGuard
    simpa only [d2301, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14362 (pattern : Twelve) (guard : d2301 pattern = 1) : d896 pattern ≤ (2 : Int) + d2326 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d896, d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14217 pattern childGuard
    simpa only [d896, d2326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d896, d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14361 pattern childGuard
    simpa only [d896, d2326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14363 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (2 : Int) + d119 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14364 (pattern : Twelve) (guard : d26 pattern = 1) : d881 pattern ≤ (2 : Int) + d119 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14363 pattern childGuard
    simpa only [d26, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14264 pattern childGuard
    simpa only [d26, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14365 (pattern : Twelve) (guard : d2301 pattern = 1) : d888 pattern ≤ (2 : Int) + d119 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14364 pattern childGuard
    simpa only [d2301, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14266 pattern childGuard
    simpa only [d2301, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14366 (pattern : Twelve) (guard : d0 pattern = 1) : d25 pattern ≤ (2 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14367 (pattern : Twelve) (guard : d26 pattern = 1) : d42 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14366 pattern childGuard
    simpa only [d26, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d26, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14368 (pattern : Twelve) (guard : d2301 pattern = 1) : d889 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14367 pattern childGuard
    simpa only [d2301, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d2301, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14369 (pattern : Twelve) (guard : d2301 pattern = 1) : d897 pattern ≤ (2 : Int) + d2327 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d897, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14365 pattern childGuard
    simpa only [d897, d2327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d897, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14368 pattern childGuard
    simpa only [d897, d2327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14370 (pattern : Twelve) (guard : d2301 pattern = 1) : d901 pattern ≤ (2 : Int) + d2328 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d901, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14362 pattern childGuard
    simpa only [d901, d2328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d901, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14369 pattern childGuard
    simpa only [d901, d2328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14371 (pattern : Twelve) (guard : d2301 pattern = 1) : d903 pattern ≤ (2 : Int) + d2329 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d903, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14355 pattern childGuard
    simpa only [d903, d2329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d903, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14370 pattern childGuard
    simpa only [d903, d2329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14372 (pattern : Twelve) (guard : d2301 pattern = 1) : d904 pattern ≤ (2 : Int) + d2323 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d904, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14347 pattern childGuard
    simpa only [d904, d2323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d904, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d904, d2323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14373 (pattern : Twelve) (guard : d2301 pattern = 1) : d905 pattern ≤ (2 : Int) + d2330 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d905, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14371 pattern childGuard
    simpa only [d905, d2330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d905, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14372 pattern childGuard
    simpa only [d905, d2330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14374 (pattern : Twelve) (guard : d2301 pattern = 1) : d906 pattern ≤ (2 : Int) + d2331 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d906, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14348 pattern childGuard
    simpa only [d906, d2331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d906, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14373 pattern childGuard
    simpa only [d906, d2331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14375 (pattern : Twelve) (guard : d2301 pattern = 1) : d907 pattern ≤ (2 : Int) + d2332 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d907, d2332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14332 pattern childGuard
    simpa only [d907, d2332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d907, d2332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14374 pattern childGuard
    simpa only [d907, d2332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14376 (pattern : Twelve) (guard : d0 pattern = 1) : d1275 pattern ≤ (2 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14377 (pattern : Twelve) (guard : d26 pattern = 1) : d1278 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14376 pattern childGuard
    simpa only [d26, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13413 pattern childGuard
    simpa only [d26, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14378 (pattern : Twelve) (guard : d0 pattern = 1) : d872 pattern ≤ (2 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14379 (pattern : Twelve) (guard : d2301 pattern = 1) : d1284 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14377 pattern childGuard
    simpa only [d2301, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14378 pattern childGuard
    simpa only [d2301, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14380 (pattern : Twelve) (guard : d2301 pattern = 1) : d1293 pattern ≤ (2 : Int) + d1976 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1293, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14289 pattern childGuard
    simpa only [d1293, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1293, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14379 pattern childGuard
    simpa only [d1293, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14381 (pattern : Twelve) (guard : d2301 pattern = 1) : d1294 pattern ≤ (2 : Int) + d1294 pattern := by
  omega
theorem c14382 (pattern : Twelve) (guard : d2301 pattern = 1) : d1305 pattern ≤ (2 : Int) + d1977 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1305, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14380 pattern childGuard
    simpa only [d1305, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1305, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14381 pattern childGuard
    simpa only [d1305, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14383 (pattern : Twelve) (guard : d26 pattern = 1) : d1279 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14376 pattern childGuard
    simpa only [d26, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13411 pattern childGuard
    simpa only [d26, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14384 (pattern : Twelve) (guard : d0 pattern = 1) : d1280 pattern ≤ (2 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14385 (pattern : Twelve) (guard : d2301 pattern = 1) : d1285 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14383 pattern childGuard
    simpa only [d2301, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14384 pattern childGuard
    simpa only [d2301, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14386 (pattern : Twelve) (guard : d2301 pattern = 1) : d1295 pattern ≤ (2 : Int) + d1976 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1295, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14302 pattern childGuard
    simpa only [d1295, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1295, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14385 pattern childGuard
    simpa only [d1295, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14387 (pattern : Twelve) (guard : d0 pattern = 1) : d19 pattern ≤ (2 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14388 (pattern : Twelve) (guard : d26 pattern = 1) : d817 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14387 pattern childGuard
    simpa only [d26, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13309 pattern childGuard
    simpa only [d26, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14389 (pattern : Twelve) (guard : d2301 pattern = 1) : d1286 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14388 pattern childGuard
    simpa only [d2301, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14178 pattern childGuard
    simpa only [d2301, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14390 (pattern : Twelve) (guard : d2301 pattern = 1) : d1296 pattern ≤ (2 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1296, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14389 pattern childGuard
    simpa only [d1296, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1296, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1296, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14391 (pattern : Twelve) (guard : d2301 pattern = 1) : d1306 pattern ≤ (2 : Int) + d1977 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1306, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14386 pattern childGuard
    simpa only [d1306, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1306, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14390 pattern childGuard
    simpa only [d1306, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14392 (pattern : Twelve) (guard : d2301 pattern = 1) : d1313 pattern ≤ (2 : Int) + d1977 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14382 pattern childGuard
    simpa only [d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14391 pattern childGuard
    simpa only [d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14393 (pattern : Twelve) (guard : d0 pattern = 1) : d1281 pattern ≤ (2 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14394 (pattern : Twelve) (guard : d2301 pattern = 1) : d1287 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14383 pattern childGuard
    simpa only [d2301, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14393 pattern childGuard
    simpa only [d2301, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14395 (pattern : Twelve) (guard : d2301 pattern = 1) : d1297 pattern ≤ (2 : Int) + d1976 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1297, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14310 pattern childGuard
    simpa only [d1297, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1297, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14394 pattern childGuard
    simpa only [d1297, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14396 (pattern : Twelve) (guard : d0 pattern = 1) : d817 pattern ≤ (2 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14397 (pattern : Twelve) (guard : d2301 pattern = 1) : d817 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14388 pattern childGuard
    simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14396 pattern childGuard
    simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14398 (pattern : Twelve) (guard : d2301 pattern = 1) : d1298 pattern ≤ (2 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1298, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14397 pattern childGuard
    simpa only [d1298, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1298, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1298, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14399 (pattern : Twelve) (guard : d2301 pattern = 1) : d1307 pattern ≤ (2 : Int) + d1977 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1307, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14395 pattern childGuard
    simpa only [d1307, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1307, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14398 pattern childGuard
    simpa only [d1307, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14400 (pattern : Twelve) (guard : d0 pattern = 1) : d1276 pattern ≤ (2 : Int) + d119 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14401 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (2 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14314 pattern childGuard
    simpa only [d1277, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13423 pattern childGuard
    simpa only [d1277, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14402 (pattern : Twelve) (guard : d26 pattern = 1) : d1282 pattern ≤ (2 : Int) + d119 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14400 pattern childGuard
    simpa only [d26, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14401 pattern childGuard
    simpa only [d26, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14403 (pattern : Twelve) (guard : d2301 pattern = 1) : d1288 pattern ≤ (2 : Int) + d119 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14402 pattern childGuard
    simpa only [d2301, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14266 pattern childGuard
    simpa only [d2301, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14404 (pattern : Twelve) (guard : d2301 pattern = 1) : d1299 pattern ≤ (2 : Int) + d2333 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1299, d2333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14321 pattern childGuard
    simpa only [d1299, d2333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1299, d2333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14403 pattern childGuard
    simpa only [d1299, d2333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14405 (pattern : Twelve) (guard : d26 pattern = 1) : d821 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13996 pattern childGuard
    simpa only [d26, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13373 pattern childGuard
    simpa only [d26, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14406 (pattern : Twelve) (guard : d2301 pattern = 1) : d1289 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14405 pattern childGuard
    simpa only [d2301, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14233 pattern childGuard
    simpa only [d2301, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14407 (pattern : Twelve) (guard : d2301 pattern = 1) : d1300 pattern ≤ (2 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1300, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14406 pattern childGuard
    simpa only [d1300, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1300, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1300, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14408 (pattern : Twelve) (guard : d2301 pattern = 1) : d1308 pattern ≤ (2 : Int) + d2334 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1308, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14404 pattern childGuard
    simpa only [d1308, d2334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1308, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14407 pattern childGuard
    simpa only [d1308, d2334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14409 (pattern : Twelve) (guard : d2301 pattern = 1) : d1314 pattern ≤ (2 : Int) + d2335 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1314, d2335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14399 pattern childGuard
    simpa only [d1314, d2335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1314, d2335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14408 pattern childGuard
    simpa only [d1314, d2335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14410 (pattern : Twelve) (guard : d2301 pattern = 1) : d1315 pattern ≤ (2 : Int) + d2336 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1315, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14391 pattern childGuard
    simpa only [d1315, d2336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1315, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1315, d2336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14411 (pattern : Twelve) (guard : d2301 pattern = 1) : d1319 pattern ≤ (2 : Int) + d2337 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1319, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14409 pattern childGuard
    simpa only [d1319, d2337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1319, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14410 pattern childGuard
    simpa only [d1319, d2337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14412 (pattern : Twelve) (guard : d2301 pattern = 1) : d1321 pattern ≤ (2 : Int) + d2338 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1321, d2338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14392 pattern childGuard
    simpa only [d1321, d2338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1321, d2338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14411 pattern childGuard
    simpa only [d1321, d2338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14413 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13320 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14414 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (2 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13283 pattern childGuard
    simpa only [d16, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d16, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14415 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14413 pattern childGuard
    simpa only [d1324, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14414 pattern childGuard
    simpa only [d1324, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14416 (pattern : Twelve) (guard : d26 pattern = 1) : d1325 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14376 pattern childGuard
    simpa only [d26, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14415 pattern childGuard
    simpa only [d26, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14417 (pattern : Twelve) (guard : d0 pattern = 1) : d1326 pattern ≤ (2 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14418 (pattern : Twelve) (guard : d2301 pattern = 1) : d1333 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14416 pattern childGuard
    simpa only [d2301, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14417 pattern childGuard
    simpa only [d2301, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14419 (pattern : Twelve) (guard : d2301 pattern = 1) : d1339 pattern ≤ (2 : Int) + d1976 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1339, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14289 pattern childGuard
    simpa only [d1339, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1339, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14418 pattern childGuard
    simpa only [d1339, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
