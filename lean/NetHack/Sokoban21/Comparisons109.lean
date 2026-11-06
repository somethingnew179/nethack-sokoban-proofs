/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons108
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c15260 (pattern : Twelve) (guard : d0 pattern = 1) : d845 pattern ≤ (1 : Int) + d830 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15261 (pattern : Twelve) (guard : d2496 pattern = 1) : d856 pattern ≤ (1 : Int) + d830 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15259 pattern childGuard
    simpa only [d2496, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15260 pattern childGuard
    simpa only [d2496, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15262 (pattern : Twelve) (guard : d2496 pattern = 1) : d862 pattern ≤ (1 : Int) + d2509 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d862, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15254 pattern childGuard
    simpa only [d862, d2509, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d862, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15261 pattern childGuard
    simpa only [d862, d2509, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15263 (pattern : Twelve) (guard : d2496 pattern = 1) : d863 pattern ≤ (1 : Int) + d2510 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d863, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15247 pattern childGuard
    simpa only [d863, d2510, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d863, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15193 pattern childGuard
    simpa only [d863, d2510, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15264 (pattern : Twelve) (guard : d2496 pattern = 1) : d867 pattern ≤ (1 : Int) + d2511 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d867, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15262 pattern childGuard
    simpa only [d867, d2511, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d867, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15263 pattern childGuard
    simpa only [d867, d2511, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15265 (pattern : Twelve) (guard : d2496 pattern = 1) : d869 pattern ≤ (1 : Int) + d2512 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d869, d2512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15248 pattern childGuard
    simpa only [d869, d2512, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d869, d2512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15264 pattern childGuard
    simpa only [d869, d2512, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15266 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (1 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15151 pattern childGuard
    simpa only [d8, d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12013 pattern childGuard
    simpa only [d8, d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15267 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15151 pattern childGuard
    simpa only [d872, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15266 pattern childGuard
    simpa only [d872, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15268 (pattern : Twelve) (guard : d1 pattern = 1) : d874 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15267 pattern childGuard
    simpa only [d874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15269 (pattern : Twelve) (guard : d1 pattern = 1) : d875 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15236 pattern childGuard
    simpa only [d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15267 pattern childGuard
    simpa only [d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15270 (pattern : Twelve) (guard : d1 pattern = 1) : d882 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15268 pattern childGuard
    simpa only [d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15269 pattern childGuard
    simpa only [d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15271 (pattern : Twelve) (guard : d1859 pattern = 1) : d890 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15232 pattern childGuard
    simpa only [d1859, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15270 pattern childGuard
    simpa only [d1859, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15272 (pattern : Twelve) (guard : d0 pattern = 1) : d891 pattern ≤ (1 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15273 (pattern : Twelve) (guard : d2496 pattern = 1) : d898 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15271 pattern childGuard
    simpa only [d2496, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15272 pattern childGuard
    simpa only [d2496, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15274 (pattern : Twelve) (guard : d1 pattern = 1) : d877 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d877, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d877, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d877, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15256 pattern childGuard
    simpa only [d877, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15275 (pattern : Twelve) (guard : d1 pattern = 1) : d884 pattern ≤ (1 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d884, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15274 pattern childGuard
    simpa only [d884, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d884, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15243 pattern childGuard
    simpa only [d884, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15276 (pattern : Twelve) (guard : d1859 pattern = 1) : d892 pattern ≤ (1 : Int) + d827 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15242 pattern childGuard
    simpa only [d1859, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15275 pattern childGuard
    simpa only [d1859, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15277 (pattern : Twelve) (guard : d0 pattern = 1) : d893 pattern ≤ (1 : Int) + d827 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15278 (pattern : Twelve) (guard : d2496 pattern = 1) : d899 pattern ≤ (1 : Int) + d827 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15276 pattern childGuard
    simpa only [d2496, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15277 pattern childGuard
    simpa only [d2496, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15279 (pattern : Twelve) (guard : d2496 pattern = 1) : d902 pattern ≤ (1 : Int) + d2508 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d902, d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15273 pattern childGuard
    simpa only [d902, d2508, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d902, d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15278 pattern childGuard
    simpa only [d902, d2508, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15280 (pattern : Twelve) (guard : d0 pattern = 1) : d30 pattern ≤ (1 : Int) + d886 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15281 (pattern : Twelve) (guard : d1 pattern = 1) : d878 pattern ≤ (1 : Int) + d879 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d878, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15236 pattern childGuard
    simpa only [d878, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d878, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12167 pattern childGuard
    simpa only [d878, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15282 (pattern : Twelve) (guard : d1 pattern = 1) : d885 pattern ≤ (1 : Int) + d886 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15274 pattern childGuard
    simpa only [d885, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15281 pattern childGuard
    simpa only [d885, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15283 (pattern : Twelve) (guard : d1859 pattern = 1) : d894 pattern ≤ (1 : Int) + d886 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15280 pattern childGuard
    simpa only [d1859, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15282 pattern childGuard
    simpa only [d1859, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15284 (pattern : Twelve) (guard : d0 pattern = 1) : d895 pattern ≤ (1 : Int) + d886 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15285 (pattern : Twelve) (guard : d2496 pattern = 1) : d900 pattern ≤ (1 : Int) + d886 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15283 pattern childGuard
    simpa only [d2496, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15284 pattern childGuard
    simpa only [d2496, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15286 (pattern : Twelve) (guard : d0 pattern = 1) : d59 pattern ≤ (1 : Int) + d888 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15287 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (1 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15217 pattern childGuard
    simpa only [d22, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11931 pattern childGuard
    simpa only [d22, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15288 (pattern : Twelve) (guard : d1 pattern = 1) : d127 pattern ≤ (1 : Int) + d881 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11132 pattern childGuard
    simpa only [d127, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15287 pattern childGuard
    simpa only [d127, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15289 (pattern : Twelve) (guard : d1 pattern = 1) : d873 pattern ≤ (1 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15220 pattern childGuard
    simpa only [d873, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11310 pattern childGuard
    simpa only [d873, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15290 (pattern : Twelve) (guard : d1 pattern = 1) : d880 pattern ≤ (1 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d880, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15289 pattern childGuard
    simpa only [d880, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d880, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d880, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15291 (pattern : Twelve) (guard : d1 pattern = 1) : d887 pattern ≤ (1 : Int) + d888 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d887, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15288 pattern childGuard
    simpa only [d887, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d887, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15290 pattern childGuard
    simpa only [d887, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15292 (pattern : Twelve) (guard : d1859 pattern = 1) : d896 pattern ≤ (1 : Int) + d888 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15286 pattern childGuard
    simpa only [d1859, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15291 pattern childGuard
    simpa only [d1859, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15293 (pattern : Twelve) (guard : d0 pattern = 1) : d897 pattern ≤ (1 : Int) + d888 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15294 (pattern : Twelve) (guard : d2496 pattern = 1) : d901 pattern ≤ (1 : Int) + d888 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15292 pattern childGuard
    simpa only [d2496, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15293 pattern childGuard
    simpa only [d2496, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15295 (pattern : Twelve) (guard : d2496 pattern = 1) : d903 pattern ≤ (1 : Int) + d2513 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d903, d2513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15285 pattern childGuard
    simpa only [d903, d2513, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d903, d2513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15294 pattern childGuard
    simpa only [d903, d2513, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15296 (pattern : Twelve) (guard : d2496 pattern = 1) : d904 pattern ≤ (1 : Int) + d2510 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d904, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15278 pattern childGuard
    simpa only [d904, d2510, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d904, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15193 pattern childGuard
    simpa only [d904, d2510, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15297 (pattern : Twelve) (guard : d2496 pattern = 1) : d905 pattern ≤ (1 : Int) + d2514 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d905, d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15295 pattern childGuard
    simpa only [d905, d2514, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d905, d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15296 pattern childGuard
    simpa only [d905, d2514, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15298 (pattern : Twelve) (guard : d2496 pattern = 1) : d906 pattern ≤ (1 : Int) + d2515 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d906, d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15279 pattern childGuard
    simpa only [d906, d2515, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d906, d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15297 pattern childGuard
    simpa only [d906, d2515, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15299 (pattern : Twelve) (guard : d2496 pattern = 1) : d907 pattern ≤ (1 : Int) + d2516 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d907, d2516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15265 pattern childGuard
    simpa only [d907, d2516, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d907, d2516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15298 pattern childGuard
    simpa only [d907, d2516, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15300 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (1 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15301 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d7, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11213 pattern childGuard
    simpa only [d7, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15302 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (1 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11212 pattern childGuard
    simpa only [d8, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d8, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15303 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15301 pattern childGuard
    simpa only [d1275, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15302 pattern childGuard
    simpa only [d1275, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15304 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15151 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11213 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15305 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15304 pattern childGuard
    simpa only [d872, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15302 pattern childGuard
    simpa only [d872, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15306 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15303 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15305 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15307 (pattern : Twelve) (guard : d1 pattern = 1) : d1284 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15306 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15305 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15308 (pattern : Twelve) (guard : d1859 pattern = 1) : d1293 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15300 pattern childGuard
    simpa only [d1859, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15307 pattern childGuard
    simpa only [d1859, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15309 (pattern : Twelve) (guard : d0 pattern = 1) : d1294 pattern ≤ (1 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15310 (pattern : Twelve) (guard : d2496 pattern = 1) : d1305 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15308 pattern childGuard
    simpa only [d2496, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15309 pattern childGuard
    simpa only [d2496, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15311 (pattern : Twelve) (guard : d0 pattern = 1) : d827 pattern ≤ (1 : Int) + d1286 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15312 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (1 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d9, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11267 pattern childGuard
    simpa only [d9, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15313 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15312 pattern childGuard
    simpa only [d1276, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11317 pattern childGuard
    simpa only [d1276, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15314 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15303 pattern childGuard
    simpa only [d1279, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15313 pattern childGuard
    simpa only [d1279, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15315 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (1 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15305 pattern childGuard
    simpa only [d1280, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d1280, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15316 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (1 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15314 pattern childGuard
    simpa only [d1285, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15315 pattern childGuard
    simpa only [d1285, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15317 (pattern : Twelve) (guard : d1859 pattern = 1) : d1295 pattern ≤ (1 : Int) + d1286 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15311 pattern childGuard
    simpa only [d1859, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15316 pattern childGuard
    simpa only [d1859, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15318 (pattern : Twelve) (guard : d0 pattern = 1) : d1296 pattern ≤ (1 : Int) + d1286 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15319 (pattern : Twelve) (guard : d2496 pattern = 1) : d1306 pattern ≤ (1 : Int) + d1286 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15317 pattern childGuard
    simpa only [d2496, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15318 pattern childGuard
    simpa only [d2496, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15320 (pattern : Twelve) (guard : d2496 pattern = 1) : d1313 pattern ≤ (1 : Int) + d2517 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1313, d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15310 pattern childGuard
    simpa only [d1313, d2517, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1313, d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15319 pattern childGuard
    simpa only [d1313, d2517, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15321 (pattern : Twelve) (guard : d0 pattern = 1) : d34 pattern ≤ (1 : Int) + d817 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15322 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15305 pattern childGuard
    simpa only [d1281, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11318 pattern childGuard
    simpa only [d1281, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15323 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15314 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15322 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15324 (pattern : Twelve) (guard : d1859 pattern = 1) : d1297 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15321 pattern childGuard
    simpa only [d1859, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15323 pattern childGuard
    simpa only [d1859, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15325 (pattern : Twelve) (guard : d0 pattern = 1) : d1298 pattern ≤ (1 : Int) + d817 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15326 (pattern : Twelve) (guard : d2496 pattern = 1) : d1307 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15324 pattern childGuard
    simpa only [d2496, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15325 pattern childGuard
    simpa only [d2496, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15327 (pattern : Twelve) (guard : d0 pattern = 1) : d830 pattern ≤ (1 : Int) + d1289 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15328 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (1 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12142 pattern childGuard
    simpa only [d15, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11234 pattern childGuard
    simpa only [d15, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15329 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (1 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15328 pattern childGuard
    simpa only [d1277, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12144 pattern childGuard
    simpa only [d1277, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15330 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15313 pattern childGuard
    simpa only [d1282, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15329 pattern childGuard
    simpa only [d1282, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15331 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11318 pattern childGuard
    simpa only [d125, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d125, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15332 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15330 pattern childGuard
    simpa only [d1288, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15331 pattern childGuard
    simpa only [d1288, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15333 (pattern : Twelve) (guard : d1859 pattern = 1) : d1299 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15327 pattern childGuard
    simpa only [d1859, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15332 pattern childGuard
    simpa only [d1859, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15334 (pattern : Twelve) (guard : d0 pattern = 1) : d1300 pattern ≤ (1 : Int) + d1289 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15335 (pattern : Twelve) (guard : d2496 pattern = 1) : d1308 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15333 pattern childGuard
    simpa only [d2496, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15334 pattern childGuard
    simpa only [d2496, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15336 (pattern : Twelve) (guard : d2496 pattern = 1) : d1314 pattern ≤ (1 : Int) + d2518 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1314, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15326 pattern childGuard
    simpa only [d1314, d2518, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1314, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15335 pattern childGuard
    simpa only [d1314, d2518, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15337 (pattern : Twelve) (guard : d2496 pattern = 1) : d1315 pattern ≤ (1 : Int) + d2519 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1315, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15319 pattern childGuard
    simpa only [d1315, d2519, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1315, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15193 pattern childGuard
    simpa only [d1315, d2519, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15338 (pattern : Twelve) (guard : d2496 pattern = 1) : d1319 pattern ≤ (1 : Int) + d2520 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1319, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15336 pattern childGuard
    simpa only [d1319, d2520, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1319, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15337 pattern childGuard
    simpa only [d1319, d2520, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15339 (pattern : Twelve) (guard : d2496 pattern = 1) : d1321 pattern ≤ (1 : Int) + d2521 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1321, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15320 pattern childGuard
    simpa only [d1321, d2521, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1321, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15338 pattern childGuard
    simpa only [d1321, d2521, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15340 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15151 pattern childGuard
    simpa only [d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15341 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15340 pattern childGuard
    simpa only [d1324, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12182 pattern childGuard
    simpa only [d1324, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15342 (pattern : Twelve) (guard : d1 pattern = 1) : d1325 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15303 pattern childGuard
    simpa only [d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15341 pattern childGuard
    simpa only [d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15343 (pattern : Twelve) (guard : d1 pattern = 1) : d1326 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15305 pattern childGuard
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15341 pattern childGuard
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15344 (pattern : Twelve) (guard : d1 pattern = 1) : d1333 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15342 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15343 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15345 (pattern : Twelve) (guard : d1859 pattern = 1) : d1339 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15300 pattern childGuard
    simpa only [d1859, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15344 pattern childGuard
    simpa only [d1859, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15346 (pattern : Twelve) (guard : d2496 pattern = 1) : d1345 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15345 pattern childGuard
    simpa only [d2496, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15309 pattern childGuard
    simpa only [d2496, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15347 (pattern : Twelve) (guard : d1 pattern = 1) : d1327 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1327, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15303 pattern childGuard
    simpa only [d1327, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1327, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11318 pattern childGuard
    simpa only [d1327, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15348 (pattern : Twelve) (guard : d1 pattern = 1) : d1334 pattern ≤ (1 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1334, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15347 pattern childGuard
    simpa only [d1334, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1334, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15315 pattern childGuard
    simpa only [d1334, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15349 (pattern : Twelve) (guard : d1859 pattern = 1) : d1340 pattern ≤ (1 : Int) + d1286 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15311 pattern childGuard
    simpa only [d1859, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15348 pattern childGuard
    simpa only [d1859, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15350 (pattern : Twelve) (guard : d2496 pattern = 1) : d1346 pattern ≤ (1 : Int) + d1286 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15349 pattern childGuard
    simpa only [d2496, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15318 pattern childGuard
    simpa only [d2496, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15351 (pattern : Twelve) (guard : d2496 pattern = 1) : d1349 pattern ≤ (1 : Int) + d2517 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1349, d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15346 pattern childGuard
    simpa only [d1349, d2517, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1349, d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15350 pattern childGuard
    simpa only [d1349, d2517, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15352 (pattern : Twelve) (guard : d0 pattern = 1) : d34 pattern ≤ (1 : Int) + d1336 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15353 (pattern : Twelve) (guard : d1 pattern = 1) : d1328 pattern ≤ (1 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1328, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15305 pattern childGuard
    simpa only [d1328, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1328, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11388 pattern childGuard
    simpa only [d1328, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15354 (pattern : Twelve) (guard : d1 pattern = 1) : d1335 pattern ≤ (1 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15347 pattern childGuard
    simpa only [d1335, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15353 pattern childGuard
    simpa only [d1335, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15355 (pattern : Twelve) (guard : d1859 pattern = 1) : d1341 pattern ≤ (1 : Int) + d1336 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15352 pattern childGuard
    simpa only [d1859, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15354 pattern childGuard
    simpa only [d1859, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15356 (pattern : Twelve) (guard : d0 pattern = 1) : d1342 pattern ≤ (1 : Int) + d1336 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15357 (pattern : Twelve) (guard : d2496 pattern = 1) : d1347 pattern ≤ (1 : Int) + d1336 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15355 pattern childGuard
    simpa only [d2496, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15356 pattern childGuard
    simpa only [d2496, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15358 (pattern : Twelve) (guard : d0 pattern = 1) : d830 pattern ≤ (1 : Int) + d1338 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15359 (pattern : Twelve) (guard : d1 pattern = 1) : d1330 pattern ≤ (1 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1330, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15313 pattern childGuard
    simpa only [d1330, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1330, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12198 pattern childGuard
    simpa only [d1330, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15360 (pattern : Twelve) (guard : d1 pattern = 1) : d1331 pattern ≤ (1 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11388 pattern childGuard
    simpa only [d1331, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d1331, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15361 (pattern : Twelve) (guard : d1 pattern = 1) : d1337 pattern ≤ (1 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1337, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15359 pattern childGuard
    simpa only [d1337, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1337, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15360 pattern childGuard
    simpa only [d1337, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15362 (pattern : Twelve) (guard : d1859 pattern = 1) : d1343 pattern ≤ (1 : Int) + d1338 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15358 pattern childGuard
    simpa only [d1859, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15361 pattern childGuard
    simpa only [d1859, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15363 (pattern : Twelve) (guard : d0 pattern = 1) : d1344 pattern ≤ (1 : Int) + d1338 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15364 (pattern : Twelve) (guard : d2496 pattern = 1) : d1348 pattern ≤ (1 : Int) + d1338 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15362 pattern childGuard
    simpa only [d2496, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15363 pattern childGuard
    simpa only [d2496, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15365 (pattern : Twelve) (guard : d2496 pattern = 1) : d1350 pattern ≤ (1 : Int) + d2522 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1350, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15357 pattern childGuard
    simpa only [d1350, d2522, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1350, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15364 pattern childGuard
    simpa only [d1350, d2522, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15366 (pattern : Twelve) (guard : d2496 pattern = 1) : d1351 pattern ≤ (1 : Int) + d2519 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1351, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15350 pattern childGuard
    simpa only [d1351, d2519, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1351, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15193 pattern childGuard
    simpa only [d1351, d2519, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15367 (pattern : Twelve) (guard : d2496 pattern = 1) : d1352 pattern ≤ (1 : Int) + d2523 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1352, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15365 pattern childGuard
    simpa only [d1352, d2523, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1352, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15366 pattern childGuard
    simpa only [d1352, d2523, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15368 (pattern : Twelve) (guard : d2496 pattern = 1) : d1353 pattern ≤ (1 : Int) + d2524 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1353, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15351 pattern childGuard
    simpa only [d1353, d2524, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1353, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15367 pattern childGuard
    simpa only [d1353, d2524, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15369 (pattern : Twelve) (guard : d2496 pattern = 1) : d1354 pattern ≤ (1 : Int) + d2525 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1354, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15339 pattern childGuard
    simpa only [d1354, d2525, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1354, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15368 pattern childGuard
    simpa only [d1354, d2525, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15370 (pattern : Twelve) (guard : d0 pattern = 1) : d19 pattern ≤ (1 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15371 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12891 pattern childGuard
    simpa only [d1324, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12734 pattern childGuard
    simpa only [d1324, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15372 (pattern : Twelve) (guard : d1859 pattern = 1) : d1649 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15370 pattern childGuard
    simpa only [d1859, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15371 pattern childGuard
    simpa only [d1859, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15373 (pattern : Twelve) (guard : d0 pattern = 1) : d1650 pattern ≤ (1 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15374 (pattern : Twelve) (guard : d2496 pattern = 1) : d1656 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15372 pattern childGuard
    simpa only [d2496, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15373 pattern childGuard
    simpa only [d2496, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15375 (pattern : Twelve) (guard : d0 pattern = 1) : d1286 pattern ≤ (1 : Int) + d1289 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15376 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15371 pattern childGuard
    simpa only [d1644, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11394 pattern childGuard
    simpa only [d1644, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15377 (pattern : Twelve) (guard : d1 pattern = 1) : d1645 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15371 pattern childGuard
    simpa only [d1645, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d1645, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15378 (pattern : Twelve) (guard : d1 pattern = 1) : d1647 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15376 pattern childGuard
    simpa only [d1647, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15377 pattern childGuard
    simpa only [d1647, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15379 (pattern : Twelve) (guard : d1859 pattern = 1) : d1651 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15375 pattern childGuard
    simpa only [d1859, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15378 pattern childGuard
    simpa only [d1859, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15380 (pattern : Twelve) (guard : d2496 pattern = 1) : d1657 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15379 pattern childGuard
    simpa only [d2496, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15334 pattern childGuard
    simpa only [d2496, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15381 (pattern : Twelve) (guard : d2496 pattern = 1) : d1660 pattern ≤ (1 : Int) + d2526 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1660, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15374 pattern childGuard
    simpa only [d1660, d2526, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1660, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15380 pattern childGuard
    simpa only [d1660, d2526, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15382 (pattern : Twelve) (guard : d0 pattern = 1) : d817 pattern ≤ (1 : Int) + d821 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15383 (pattern : Twelve) (guard : d1859 pattern = 1) : d1652 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15382 pattern childGuard
    simpa only [d1859, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15376 pattern childGuard
    simpa only [d1859, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15384 (pattern : Twelve) (guard : d0 pattern = 1) : d1653 pattern ≤ (1 : Int) + d821 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15385 (pattern : Twelve) (guard : d2496 pattern = 1) : d1658 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15383 pattern childGuard
    simpa only [d2496, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15384 pattern childGuard
    simpa only [d2496, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15386 (pattern : Twelve) (guard : d0 pattern = 1) : d1289 pattern ≤ (1 : Int) + d822 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15387 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11394 pattern childGuard
    simpa only [d1646, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11431 pattern childGuard
    simpa only [d1646, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15388 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11394 pattern childGuard
    simpa only [d128, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d128, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15389 (pattern : Twelve) (guard : d1 pattern = 1) : d1648 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15387 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15388 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15390 (pattern : Twelve) (guard : d1859 pattern = 1) : d1654 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15386 pattern childGuard
    simpa only [d1859, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15389 pattern childGuard
    simpa only [d1859, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15391 (pattern : Twelve) (guard : d0 pattern = 1) : d1655 pattern ≤ (1 : Int) + d822 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15392 (pattern : Twelve) (guard : d2496 pattern = 1) : d1659 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15390 pattern childGuard
    simpa only [d2496, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15391 pattern childGuard
    simpa only [d2496, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15393 (pattern : Twelve) (guard : d2496 pattern = 1) : d1661 pattern ≤ (1 : Int) + d2527 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1661, d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15385 pattern childGuard
    simpa only [d1661, d2527, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1661, d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15392 pattern childGuard
    simpa only [d1661, d2527, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15394 (pattern : Twelve) (guard : d2496 pattern = 1) : d1662 pattern ≤ (1 : Int) + d2528 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1662, d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15380 pattern childGuard
    simpa only [d1662, d2528, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1662, d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15193 pattern childGuard
    simpa only [d1662, d2528, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15395 (pattern : Twelve) (guard : d2496 pattern = 1) : d1663 pattern ≤ (1 : Int) + d2529 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1663, d2529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15393 pattern childGuard
    simpa only [d1663, d2529, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1663, d2529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15394 pattern childGuard
    simpa only [d1663, d2529, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15396 (pattern : Twelve) (guard : d2496 pattern = 1) : d1664 pattern ≤ (1 : Int) + d2530 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1664, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15381 pattern childGuard
    simpa only [d1664, d2530, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1664, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15395 pattern childGuard
    simpa only [d1664, d2530, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15397 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15371 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11199 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15398 (pattern : Twelve) (guard : d1859 pattern = 1) : d1668 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15370 pattern childGuard
    simpa only [d1859, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15397 pattern childGuard
    simpa only [d1859, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15399 (pattern : Twelve) (guard : d2496 pattern = 1) : d1671 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15398 pattern childGuard
    simpa only [d2496, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15373 pattern childGuard
    simpa only [d2496, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
