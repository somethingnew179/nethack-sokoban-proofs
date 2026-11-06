/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons094
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c13300 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (2 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13299 pattern childGuard
    simpa only [d40, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d40, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13301 (pattern : Twelve) (guard : d1 pattern = 1) : d60 pattern ≤ (2 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13294 pattern childGuard
    simpa only [d60, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13300 pattern childGuard
    simpa only [d60, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13302 (pattern : Twelve) (guard : d1 pattern = 1) : d81 pattern ≤ (2 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13297 pattern childGuard
    simpa only [d81, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13301 pattern childGuard
    simpa only [d81, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13303 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (2 : Int) + d3 pattern := by
  change (5 : Int) ≤ (2 : Int) + 3
  decide
theorem c13304 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (2 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d15, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13303 pattern childGuard
    simpa only [d15, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13305 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d24, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13304 pattern childGuard
    simpa only [d24, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13306 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (2 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13299 pattern childGuard
    simpa only [d41, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13305 pattern childGuard
    simpa only [d41, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13307 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13281 pattern childGuard
    simpa only [d16, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d16, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13308 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (2 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d12, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13303 pattern childGuard
    simpa only [d12, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13309 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13307 pattern childGuard
    simpa only [d25, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13308 pattern childGuard
    simpa only [d25, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13310 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (2 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13309 pattern childGuard
    simpa only [d42, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d42, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13311 (pattern : Twelve) (guard : d1 pattern = 1) : d61 pattern ≤ (2 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13306 pattern childGuard
    simpa only [d61, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13310 pattern childGuard
    simpa only [d61, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13312 (pattern : Twelve) (guard : d1 pattern = 1) : d82 pattern ≤ (2 : Int) + d78 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13297 pattern childGuard
    simpa only [d82, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13311 pattern childGuard
    simpa only [d82, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13313 (pattern : Twelve) (guard : d1 pattern = 1) : d96 pattern ≤ (2 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13302 pattern childGuard
    simpa only [d96, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13312 pattern childGuard
    simpa only [d96, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13314 (pattern : Twelve) (guard : d1 pattern = 1) : d104 pattern ≤ (2 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13292 pattern childGuard
    simpa only [d104, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13313 pattern childGuard
    simpa only [d104, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13315 (pattern : Twelve) (guard : d0 pattern = 1) : d105 pattern ≤ (2 : Int) + d103 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13316 (pattern : Twelve) (guard : d1835 pattern = 1) : d111 pattern ≤ (2 : Int) + d103 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13314 pattern childGuard
    simpa only [d1835, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13315 pattern childGuard
    simpa only [d1835, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13317 (pattern : Twelve) (guard : d2266 pattern = 1) : d114 pattern ≤ (2 : Int) + d103 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13279 pattern childGuard
    simpa only [d2266, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13316 pattern childGuard
    simpa only [d2266, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13318 (pattern : Twelve) (guard : d0 pattern = 1) : d112 pattern ≤ (2 : Int) + d107 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13319 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d0 pattern := by
  change (1 : Int) ≤ (2 : Int) + 0
  decide
theorem c13320 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d1 pattern := by
  omega
theorem c13321 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13319 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13320 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13322 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13319 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13321 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13323 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (2 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13322 pattern childGuard
    simpa only [d46, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d46, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13324 (pattern : Twelve) (guard : d1 pattern = 1) : d67 pattern ≤ (2 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13284 pattern childGuard
    simpa only [d67, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13323 pattern childGuard
    simpa only [d67, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13325 (pattern : Twelve) (guard : d1 pattern = 1) : d87 pattern ≤ (2 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13282 pattern childGuard
    simpa only [d87, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13324 pattern childGuard
    simpa only [d87, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13326 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (2 : Int) + d30 pattern := by
  omega
theorem c13327 (pattern : Twelve) (guard : d1 pattern = 1) : d68 pattern ≤ (2 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13294 pattern childGuard
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13328 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (2 : Int) + d34 pattern := by
  omega
theorem c13329 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d2 pattern := by
  omega
theorem c13330 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13281 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13331 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d3 pattern := by
  omega
theorem c13332 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (2 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13283 pattern childGuard
    simpa only [d9, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13331 pattern childGuard
    simpa only [d9, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13333 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13330 pattern childGuard
    simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13332 pattern childGuard
    simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13334 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (2 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13333 pattern childGuard
    simpa only [d40, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d40, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13335 (pattern : Twelve) (guard : d1 pattern = 1) : d64 pattern ≤ (2 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13328 pattern childGuard
    simpa only [d64, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13334 pattern childGuard
    simpa only [d64, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13336 (pattern : Twelve) (guard : d1 pattern = 1) : d88 pattern ≤ (2 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13327 pattern childGuard
    simpa only [d88, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13335 pattern childGuard
    simpa only [d88, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13337 (pattern : Twelve) (guard : d1 pattern = 1) : d100 pattern ≤ (2 : Int) + d97 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13325 pattern childGuard
    simpa only [d100, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13336 pattern childGuard
    simpa only [d100, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13338 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (2 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d47, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d47, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13339 (pattern : Twelve) (guard : d1 pattern = 1) : d69 pattern ≤ (2 : Int) + d65 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13294 pattern childGuard
    simpa only [d69, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13338 pattern childGuard
    simpa only [d69, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13340 (pattern : Twelve) (guard : d1 pattern = 1) : d89 pattern ≤ (2 : Int) + d85 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13297 pattern childGuard
    simpa only [d89, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13339 pattern childGuard
    simpa only [d89, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13341 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (2 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d48, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d48, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13342 (pattern : Twelve) (guard : d1 pattern = 1) : d70 pattern ≤ (2 : Int) + d66 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13294 pattern childGuard
    simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13341 pattern childGuard
    simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13343 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (2 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13305 pattern childGuard
    simpa only [d49, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d49, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13344 (pattern : Twelve) (guard : d1 pattern = 1) : d71 pattern ≤ (2 : Int) + d64 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13306 pattern childGuard
    simpa only [d71, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13343 pattern childGuard
    simpa only [d71, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13345 (pattern : Twelve) (guard : d1 pattern = 1) : d90 pattern ≤ (2 : Int) + d86 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13342 pattern childGuard
    simpa only [d90, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13344 pattern childGuard
    simpa only [d90, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13346 (pattern : Twelve) (guard : d1 pattern = 1) : d101 pattern ≤ (2 : Int) + d99 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13340 pattern childGuard
    simpa only [d101, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13345 pattern childGuard
    simpa only [d101, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13347 (pattern : Twelve) (guard : d1 pattern = 1) : d108 pattern ≤ (2 : Int) + d107 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13337 pattern childGuard
    simpa only [d108, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13346 pattern childGuard
    simpa only [d108, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13348 (pattern : Twelve) (guard : d0 pattern = 1) : d109 pattern ≤ (2 : Int) + d107 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13349 (pattern : Twelve) (guard : d1835 pattern = 1) : d113 pattern ≤ (2 : Int) + d107 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13347 pattern childGuard
    simpa only [d1835, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13348 pattern childGuard
    simpa only [d1835, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13350 (pattern : Twelve) (guard : d2266 pattern = 1) : d115 pattern ≤ (2 : Int) + d107 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13318 pattern childGuard
    simpa only [d2266, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13349 pattern childGuard
    simpa only [d2266, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13351 (pattern : Twelve) (guard : d2266 pattern = 1) : d116 pattern ≤ (2 : Int) + d2267 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2266 pattern = 1 := by simpa only [d116, d2267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13317 pattern childGuard
    simpa only [d116, d2267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2266 pattern = 1 := by simpa only [d116, d2267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13350 pattern childGuard
    simpa only [d116, d2267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13352 (pattern : Twelve) (guard : d0 pattern = 1) : d861 pattern ≤ (2 : Int) + d861 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13353 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13283 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13354 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13283 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13353 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13355 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (2 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d34, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13354 pattern childGuard
    simpa only [d34, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13356 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (2 : Int) + d814 pattern := by
  omega
theorem c13357 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (2 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13356 pattern childGuard
    simpa only [d819, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d819, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13358 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (2 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13355 pattern childGuard
    simpa only [d828, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13357 pattern childGuard
    simpa only [d828, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13359 (pattern : Twelve) (guard : d1 pattern = 1) : d842 pattern ≤ (2 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13282 pattern childGuard
    simpa only [d842, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13358 pattern childGuard
    simpa only [d842, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13360 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13299 pattern childGuard
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13361 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (2 : Int) + d825 pattern := by
  omega
theorem c13362 (pattern : Twelve) (guard : d1 pattern = 1) : d843 pattern ≤ (2 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13360 pattern childGuard
    simpa only [d843, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13361 pattern childGuard
    simpa only [d843, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13363 (pattern : Twelve) (guard : d1 pattern = 1) : d855 pattern ≤ (2 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13359 pattern childGuard
    simpa only [d855, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13362 pattern childGuard
    simpa only [d855, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13364 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (2 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13298 pattern childGuard
    simpa only [d815, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d815, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13365 (pattern : Twelve) (guard : d1 pattern = 1) : d820 pattern ≤ (2 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13364 pattern childGuard
    simpa only [d820, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d820, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13366 (pattern : Twelve) (guard : d1 pattern = 1) : d829 pattern ≤ (2 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13306 pattern childGuard
    simpa only [d829, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13365 pattern childGuard
    simpa only [d829, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13367 (pattern : Twelve) (guard : d1 pattern = 1) : d844 pattern ≤ (2 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13297 pattern childGuard
    simpa only [d844, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13366 pattern childGuard
    simpa only [d844, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13368 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (2 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13306 pattern childGuard
    simpa only [d830, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13300 pattern childGuard
    simpa only [d830, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13369 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d4 pattern := by
  change (6 : Int) ≤ (2 : Int) + 4
  decide
theorem c13370 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (2 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d13, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13369 pattern childGuard
    simpa only [d13, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13371 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d5 pattern := by
  change (6 : Int) ≤ (2 : Int) + 5
  decide
theorem c13372 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (2 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13303 pattern childGuard
    simpa only [d14, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13371 pattern childGuard
    simpa only [d14, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13373 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13370 pattern childGuard
    simpa only [d21, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13372 pattern childGuard
    simpa only [d21, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13374 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (2 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13309 pattern childGuard
    simpa only [d821, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13373 pattern childGuard
    simpa only [d821, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13375 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (2 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13373 pattern childGuard
    simpa only [d822, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d822, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13376 (pattern : Twelve) (guard : d1 pattern = 1) : d831 pattern ≤ (2 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13374 pattern childGuard
    simpa only [d831, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13375 pattern childGuard
    simpa only [d831, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13377 (pattern : Twelve) (guard : d1 pattern = 1) : d845 pattern ≤ (2 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13368 pattern childGuard
    simpa only [d845, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13376 pattern childGuard
    simpa only [d845, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13378 (pattern : Twelve) (guard : d1 pattern = 1) : d856 pattern ≤ (2 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13367 pattern childGuard
    simpa only [d856, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13377 pattern childGuard
    simpa only [d856, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13379 (pattern : Twelve) (guard : d1 pattern = 1) : d862 pattern ≤ (2 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13363 pattern childGuard
    simpa only [d862, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13378 pattern childGuard
    simpa only [d862, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13380 (pattern : Twelve) (guard : d0 pattern = 1) : d863 pattern ≤ (2 : Int) + d861 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13381 (pattern : Twelve) (guard : d1835 pattern = 1) : d867 pattern ≤ (2 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13379 pattern childGuard
    simpa only [d1835, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13380 pattern childGuard
    simpa only [d1835, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13382 (pattern : Twelve) (guard : d2266 pattern = 1) : d869 pattern ≤ (2 : Int) + d861 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13352 pattern childGuard
    simpa only [d2266, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13381 pattern childGuard
    simpa only [d2266, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13383 (pattern : Twelve) (guard : d0 pattern = 1) : d864 pattern ≤ (2 : Int) + d864 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13384 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13321 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13320 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13385 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (2 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13384 pattern childGuard
    simpa only [d46, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d46, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13386 (pattern : Twelve) (guard : d1 pattern = 1) : d834 pattern ≤ (2 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13355 pattern childGuard
    simpa only [d834, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13385 pattern childGuard
    simpa only [d834, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13387 (pattern : Twelve) (guard : d1 pattern = 1) : d849 pattern ≤ (2 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13282 pattern childGuard
    simpa only [d849, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13386 pattern childGuard
    simpa only [d849, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13388 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d2 pattern := by
  change (3 : Int) ≤ (2 : Int) + 2
  decide
theorem c13389 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13388 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13390 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13389 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13391 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (2 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d34, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13390 pattern childGuard
    simpa only [d34, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13392 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13281 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13283 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13393 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13281 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13392 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13394 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (2 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13393 pattern childGuard
    simpa only [d38, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d38, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13395 (pattern : Twelve) (guard : d1 pattern = 1) : d835 pattern ≤ (2 : Int) + d823 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13391 pattern childGuard
    simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13394 pattern childGuard
    simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13396 (pattern : Twelve) (guard : d1 pattern = 1) : d850 pattern ≤ (2 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13395 pattern childGuard
    simpa only [d850, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13361 pattern childGuard
    simpa only [d850, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13397 (pattern : Twelve) (guard : d1 pattern = 1) : d859 pattern ≤ (2 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13387 pattern childGuard
    simpa only [d859, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13396 pattern childGuard
    simpa only [d859, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13398 (pattern : Twelve) (guard : d1 pattern = 1) : d836 pattern ≤ (2 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13306 pattern childGuard
    simpa only [d836, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13338 pattern childGuard
    simpa only [d836, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13399 (pattern : Twelve) (guard : d1 pattern = 1) : d851 pattern ≤ (2 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13297 pattern childGuard
    simpa only [d851, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13398 pattern childGuard
    simpa only [d851, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13400 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (2 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13306 pattern childGuard
    simpa only [d837, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13341 pattern childGuard
    simpa only [d837, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13401 (pattern : Twelve) (guard : d1 pattern = 1) : d852 pattern ≤ (2 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13400 pattern childGuard
    simpa only [d852, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13376 pattern childGuard
    simpa only [d852, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13402 (pattern : Twelve) (guard : d1 pattern = 1) : d860 pattern ≤ (2 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13399 pattern childGuard
    simpa only [d860, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13401 pattern childGuard
    simpa only [d860, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13403 (pattern : Twelve) (guard : d1 pattern = 1) : d865 pattern ≤ (2 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13397 pattern childGuard
    simpa only [d865, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13402 pattern childGuard
    simpa only [d865, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13404 (pattern : Twelve) (guard : d0 pattern = 1) : d866 pattern ≤ (2 : Int) + d864 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13405 (pattern : Twelve) (guard : d1835 pattern = 1) : d868 pattern ≤ (2 : Int) + d864 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13403 pattern childGuard
    simpa only [d1835, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13404 pattern childGuard
    simpa only [d1835, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13406 (pattern : Twelve) (guard : d2266 pattern = 1) : d870 pattern ≤ (2 : Int) + d864 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13383 pattern childGuard
    simpa only [d2266, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13405 pattern childGuard
    simpa only [d2266, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13407 (pattern : Twelve) (guard : d2266 pattern = 1) : d871 pattern ≤ (2 : Int) + d2268 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2266 pattern = 1 := by simpa only [d871, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13382 pattern childGuard
    simpa only [d871, d2268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2266 pattern = 1 := by simpa only [d871, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13406 pattern childGuard
    simpa only [d871, d2268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13408 (pattern : Twelve) (guard : d0 pattern = 1) : d1313 pattern ≤ (2 : Int) + d1313 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13409 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (2 : Int) + d1275 pattern := by
  omega
theorem c13410 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (2 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d117, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d117, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13411 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13353 pattern childGuard
    simpa only [d1276, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13410 pattern childGuard
    simpa only [d1276, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13412 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (2 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13409 pattern childGuard
    simpa only [d1279, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13411 pattern childGuard
    simpa only [d1279, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13413 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (2 : Int) + d872 pattern := by
  omega
theorem c13414 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d119, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13410 pattern childGuard
    simpa only [d119, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13415 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13413 pattern childGuard
    simpa only [d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13414 pattern childGuard
    simpa only [d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13416 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (2 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13412 pattern childGuard
    simpa only [d1287, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13415 pattern childGuard
    simpa only [d1287, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13417 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (2 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13360 pattern childGuard
    simpa only [d1297, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13416 pattern childGuard
    simpa only [d1297, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13418 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (2 : Int) + d19 pattern := by
  omega
theorem c13419 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13418 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13309 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13420 (pattern : Twelve) (guard : d1 pattern = 1) : d1298 pattern ≤ (2 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13419 pattern childGuard
    simpa only [d1298, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1298, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13421 (pattern : Twelve) (guard : d1 pattern = 1) : d1307 pattern ≤ (2 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13417 pattern childGuard
    simpa only [d1307, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13420 pattern childGuard
    simpa only [d1307, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13422 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (2 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13298 pattern childGuard
    simpa only [d1276, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13410 pattern childGuard
    simpa only [d1276, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13423 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (2 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13303 pattern childGuard
    simpa only [d14, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13369 pattern childGuard
    simpa only [d14, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13424 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (2 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13304 pattern childGuard
    simpa only [d1277, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13423 pattern childGuard
    simpa only [d1277, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13425 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (2 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13422 pattern childGuard
    simpa only [d1282, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13424 pattern childGuard
    simpa only [d1282, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13426 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (2 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13414 pattern childGuard
    simpa only [d125, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d125, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13427 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (2 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13425 pattern childGuard
    simpa only [d1288, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13426 pattern childGuard
    simpa only [d1288, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13428 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (2 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13368 pattern childGuard
    simpa only [d1299, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13427 pattern childGuard
    simpa only [d1299, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13429 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (2 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13374 pattern childGuard
    simpa only [d1289, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13310 pattern childGuard
    simpa only [d1289, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13430 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (2 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13429 pattern childGuard
    simpa only [d1300, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1300, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13431 (pattern : Twelve) (guard : d1 pattern = 1) : d1308 pattern ≤ (2 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13428 pattern childGuard
    simpa only [d1308, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13430 pattern childGuard
    simpa only [d1308, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13432 (pattern : Twelve) (guard : d1 pattern = 1) : d1314 pattern ≤ (2 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13421 pattern childGuard
    simpa only [d1314, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13431 pattern childGuard
    simpa only [d1314, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13433 (pattern : Twelve) (guard : d0 pattern = 1) : d1315 pattern ≤ (2 : Int) + d1313 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13434 (pattern : Twelve) (guard : d1835 pattern = 1) : d1319 pattern ≤ (2 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13432 pattern childGuard
    simpa only [d1835, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13433 pattern childGuard
    simpa only [d1835, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13435 (pattern : Twelve) (guard : d2266 pattern = 1) : d1321 pattern ≤ (2 : Int) + d1313 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13408 pattern childGuard
    simpa only [d2266, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13434 pattern childGuard
    simpa only [d2266, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13436 (pattern : Twelve) (guard : d0 pattern = 1) : d1316 pattern ≤ (2 : Int) + d1316 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13437 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13438 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (2 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13388 pattern childGuard
    simpa only [d12, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13303 pattern childGuard
    simpa only [d12, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13439 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13437 pattern childGuard
    simpa only [d25, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13438 pattern childGuard
    simpa only [d25, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
