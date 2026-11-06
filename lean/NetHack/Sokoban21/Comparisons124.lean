/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons123
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c17360 (pattern : Twelve) (guard : d0 pattern = 1) : d60 pattern ≤ (1 : Int) + d60 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17361 (pattern : Twelve) (guard : d1852 pattern = 1) : d81 pattern ≤ (1 : Int) + d60 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12005 pattern childGuard
    simpa only [d1852, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17360 pattern childGuard
    simpa only [d1852, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17362 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (1 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12142 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12489 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17363 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (1 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11139 pattern childGuard
    simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17362 pattern childGuard
    simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17364 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d5 pattern := by
  change (2 : Int) ≤ (1 : Int) + 5
  decide
theorem c17365 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17364 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17366 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11275 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17365 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17367 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17366 pattern childGuard
    simpa only [d39, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d39, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17368 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (1 : Int) + d61 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17363 pattern childGuard
    simpa only [d59, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17367 pattern childGuard
    simpa only [d59, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17369 (pattern : Twelve) (guard : d0 pattern = 1) : d61 pattern ≤ (1 : Int) + d61 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17370 (pattern : Twelve) (guard : d1852 pattern = 1) : d82 pattern ≤ (1 : Int) + d61 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17368 pattern childGuard
    simpa only [d1852, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17369 pattern childGuard
    simpa only [d1852, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17371 (pattern : Twelve) (guard : d1852 pattern = 1) : d96 pattern ≤ (1 : Int) + d3169 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d96, d3169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17361 pattern childGuard
    simpa only [d96, d3169, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d96, d3169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17370 pattern childGuard
    simpa only [d96, d3169, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17372 (pattern : Twelve) (guard : d1852 pattern = 1) : d104 pattern ≤ (1 : Int) + d3170 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d104, d3170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17359 pattern childGuard
    simpa only [d104, d3170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d104, d3170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17371 pattern childGuard
    simpa only [d104, d3170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17373 (pattern : Twelve) (guard : d1852 pattern = 1) : d6 pattern ≤ (1 : Int) + d6 pattern := by
  omega
theorem c17374 (pattern : Twelve) (guard : d1852 pattern = 1) : d105 pattern ≤ (1 : Int) + d3171 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d105, d3171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17351 pattern childGuard
    simpa only [d105, d3171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d105, d3171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17373 pattern childGuard
    simpa only [d105, d3171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17375 (pattern : Twelve) (guard : d1852 pattern = 1) : d111 pattern ≤ (1 : Int) + d3172 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d111, d3172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17372 pattern childGuard
    simpa only [d111, d3172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d111, d3172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17374 pattern childGuard
    simpa only [d111, d3172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17376 (pattern : Twelve) (guard : d1852 pattern = 1) : d114 pattern ≤ (1 : Int) + d3173 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d114, d3173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17353 pattern childGuard
    simpa only [d114, d3173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d114, d3173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17375 pattern childGuard
    simpa only [d114, d3173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17377 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d4 pattern := by
  change (0 : Int) ≤ (1 : Int) + 4
  decide
theorem c17378 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11221 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17377 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17379 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d5 pattern := by
  change (0 : Int) ≤ (1 : Int) + 5
  decide
theorem c17380 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17319 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17379 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17381 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17378 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17380 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17382 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d120 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17381 pattern childGuard
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17383 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17382 pattern childGuard
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17325 pattern childGuard
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17384 (pattern : Twelve) (guard : d0 pattern = 1) : d129 pattern ≤ (1 : Int) + d129 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17385 (pattern : Twelve) (guard : d1852 pattern = 1) : d136 pattern ≤ (1 : Int) + d129 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17383 pattern childGuard
    simpa only [d1852, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17384 pattern childGuard
    simpa only [d1852, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17386 (pattern : Twelve) (guard : d1852 pattern = 1) : d144 pattern ≤ (1 : Int) + d3174 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d144, d3174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17317 pattern childGuard
    simpa only [d144, d3174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d144, d3174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17385 pattern childGuard
    simpa only [d144, d3174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17387 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d121 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d30, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11139 pattern childGuard
    simpa only [d30, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17388 (pattern : Twelve) (guard : d1 pattern = 1) : d31 pattern ≤ (1 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d31, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11419 pattern childGuard
    simpa only [d31, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17389 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (1 : Int) + d130 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17387 pattern childGuard
    simpa only [d52, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17388 pattern childGuard
    simpa only [d52, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17390 (pattern : Twelve) (guard : d0 pattern = 1) : d130 pattern ≤ (1 : Int) + d130 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17391 (pattern : Twelve) (guard : d1852 pattern = 1) : d137 pattern ≤ (1 : Int) + d130 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17389 pattern childGuard
    simpa only [d1852, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17390 pattern childGuard
    simpa only [d1852, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17392 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d120 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d30, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17366 pattern childGuard
    simpa only [d30, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17393 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (1 : Int) + d129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17392 pattern childGuard
    simpa only [d56, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17348 pattern childGuard
    simpa only [d56, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17394 (pattern : Twelve) (guard : d1852 pattern = 1) : d138 pattern ≤ (1 : Int) + d129 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17393 pattern childGuard
    simpa only [d1852, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17384 pattern childGuard
    simpa only [d1852, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17395 (pattern : Twelve) (guard : d1852 pattern = 1) : d145 pattern ≤ (1 : Int) + d3175 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d145, d3175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17391 pattern childGuard
    simpa only [d145, d3175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d145, d3175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17394 pattern childGuard
    simpa only [d145, d3175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17396 (pattern : Twelve) (guard : d1852 pattern = 1) : d149 pattern ≤ (1 : Int) + d3176 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d149, d3176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17386 pattern childGuard
    simpa only [d149, d3176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d149, d3176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17395 pattern childGuard
    simpa only [d149, d3176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17397 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (1 : Int) + d130 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17387 pattern childGuard
    simpa only [d56, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11989 pattern childGuard
    simpa only [d56, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17398 (pattern : Twelve) (guard : d1852 pattern = 1) : d139 pattern ≤ (1 : Int) + d130 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17397 pattern childGuard
    simpa only [d1852, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17390 pattern childGuard
    simpa only [d1852, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17399 (pattern : Twelve) (guard : d1852 pattern = 1) : d146 pattern ≤ (1 : Int) + d3175 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d146, d3175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17398 pattern childGuard
    simpa only [d146, d3175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d146, d3175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17394 pattern childGuard
    simpa only [d146, d3175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17400 (pattern : Twelve) (guard : d1852 pattern = 1) : d150 pattern ≤ (1 : Int) + d3176 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d150, d3176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17386 pattern childGuard
    simpa only [d150, d3176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d150, d3176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17399 pattern childGuard
    simpa only [d150, d3176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17401 (pattern : Twelve) (guard : d1852 pattern = 1) : d153 pattern ≤ (1 : Int) + d3176 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17396 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17400 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17402 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d122 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d30, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11274 pattern childGuard
    simpa only [d30, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17403 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d131 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17387 pattern childGuard
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17402 pattern childGuard
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17404 (pattern : Twelve) (guard : d0 pattern = 1) : d131 pattern ≤ (1 : Int) + d131 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17405 (pattern : Twelve) (guard : d1852 pattern = 1) : d140 pattern ≤ (1 : Int) + d131 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17403 pattern childGuard
    simpa only [d1852, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17404 pattern childGuard
    simpa only [d1852, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17406 (pattern : Twelve) (guard : d1 pattern = 1) : d123 pattern ≤ (1 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d123, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17324 pattern childGuard
    simpa only [d123, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d123, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11233 pattern childGuard
    simpa only [d123, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17407 (pattern : Twelve) (guard : d1 pattern = 1) : d132 pattern ≤ (1 : Int) + d129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17392 pattern childGuard
    simpa only [d132, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17406 pattern childGuard
    simpa only [d132, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17408 (pattern : Twelve) (guard : d1852 pattern = 1) : d141 pattern ≤ (1 : Int) + d129 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17407 pattern childGuard
    simpa only [d1852, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17384 pattern childGuard
    simpa only [d1852, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17409 (pattern : Twelve) (guard : d1852 pattern = 1) : d147 pattern ≤ (1 : Int) + d3177 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d147, d3177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17405 pattern childGuard
    simpa only [d147, d3177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d147, d3177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17408 pattern childGuard
    simpa only [d147, d3177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17410 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (1 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11316 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11231 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17411 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (1 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11316 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17410 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17412 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (1 : Int) + d124 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d38, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17411 pattern childGuard
    simpa only [d38, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17413 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11274 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17414 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17413 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17415 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (1 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17414 pattern childGuard
    simpa only [d39, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d39, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17416 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (1 : Int) + d133 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17412 pattern childGuard
    simpa only [d59, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17415 pattern childGuard
    simpa only [d59, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17417 (pattern : Twelve) (guard : d0 pattern = 1) : d133 pattern ≤ (1 : Int) + d133 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17418 (pattern : Twelve) (guard : d1852 pattern = 1) : d142 pattern ≤ (1 : Int) + d133 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17416 pattern childGuard
    simpa only [d1852, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17417 pattern childGuard
    simpa only [d1852, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17419 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (1 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12426 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11234 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17420 (pattern : Twelve) (guard : d1 pattern = 1) : d126 pattern ≤ (1 : Int) + d127 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d126, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11139 pattern childGuard
    simpa only [d126, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d126, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17419 pattern childGuard
    simpa only [d126, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17421 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (1 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11267 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11233 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17422 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (1 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11363 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17421 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17423 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (1 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17422 pattern childGuard
    simpa only [d47, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d47, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17424 (pattern : Twelve) (guard : d1 pattern = 1) : d134 pattern ≤ (1 : Int) + d135 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d134, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17420 pattern childGuard
    simpa only [d134, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d134, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17423 pattern childGuard
    simpa only [d134, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17425 (pattern : Twelve) (guard : d0 pattern = 1) : d135 pattern ≤ (1 : Int) + d135 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17426 (pattern : Twelve) (guard : d1852 pattern = 1) : d143 pattern ≤ (1 : Int) + d135 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17424 pattern childGuard
    simpa only [d1852, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17425 pattern childGuard
    simpa only [d1852, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17427 (pattern : Twelve) (guard : d1852 pattern = 1) : d148 pattern ≤ (1 : Int) + d3178 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d148, d3178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17418 pattern childGuard
    simpa only [d148, d3178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d148, d3178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17426 pattern childGuard
    simpa only [d148, d3178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17428 (pattern : Twelve) (guard : d1852 pattern = 1) : d151 pattern ≤ (1 : Int) + d3179 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d151, d3179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17409 pattern childGuard
    simpa only [d151, d3179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d151, d3179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17427 pattern childGuard
    simpa only [d151, d3179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17429 (pattern : Twelve) (guard : d1852 pattern = 1) : d152 pattern ≤ (1 : Int) + d3180 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d152, d3180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17399 pattern childGuard
    simpa only [d152, d3180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d152, d3180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17373 pattern childGuard
    simpa only [d152, d3180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17430 (pattern : Twelve) (guard : d1852 pattern = 1) : d154 pattern ≤ (1 : Int) + d3181 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d154, d3181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17428 pattern childGuard
    simpa only [d154, d3181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d154, d3181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17429 pattern childGuard
    simpa only [d154, d3181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17431 (pattern : Twelve) (guard : d1852 pattern = 1) : d155 pattern ≤ (1 : Int) + d3182 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d155, d3182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17401 pattern childGuard
    simpa only [d155, d3182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d155, d3182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17430 pattern childGuard
    simpa only [d155, d3182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17432 (pattern : Twelve) (guard : d1852 pattern = 1) : d156 pattern ≤ (1 : Int) + d3183 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d156, d3183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17376 pattern childGuard
    simpa only [d156, d3183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d156, d3183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17431 pattern childGuard
    simpa only [d156, d3183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17433 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11061 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11060 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17434 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17433 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11060 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17435 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11973 pattern childGuard
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17434 pattern childGuard
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17436 (pattern : Twelve) (guard : d0 pattern = 1) : d824 pattern ≤ (1 : Int) + d824 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17437 (pattern : Twelve) (guard : d1852 pattern = 1) : d838 pattern ≤ (1 : Int) + d824 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17435 pattern childGuard
    simpa only [d1852, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17436 pattern childGuard
    simpa only [d1852, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17438 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (1 : Int) + d5 pattern := by
  change (1 : Int) ≤ (1 : Int) + 5
  decide
theorem c17439 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17319 pattern childGuard
    simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17438 pattern childGuard
    simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17440 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17378 pattern childGuard
    simpa only [d17, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17439 pattern childGuard
    simpa only [d17, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17441 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11225 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17440 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17442 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11403 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11405 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17443 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11403 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17442 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17444 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17440 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17443 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17445 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17441 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17444 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17446 (pattern : Twelve) (guard : d0 pattern = 1) : d825 pattern ≤ (1 : Int) + d825 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17447 (pattern : Twelve) (guard : d1852 pattern = 1) : d839 pattern ≤ (1 : Int) + d825 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17445 pattern childGuard
    simpa only [d1852, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17446 pattern childGuard
    simpa only [d1852, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17448 (pattern : Twelve) (guard : d1852 pattern = 1) : d853 pattern ≤ (1 : Int) + d3184 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d853, d3184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17437 pattern childGuard
    simpa only [d853, d3184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d853, d3184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17447 pattern childGuard
    simpa only [d853, d3184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17449 (pattern : Twelve) (guard : d1 pattern = 1) : d35 pattern ≤ (1 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17433 pattern childGuard
    simpa only [d35, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d35, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17450 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (1 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17334 pattern childGuard
    simpa only [d56, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17449 pattern childGuard
    simpa only [d56, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17451 (pattern : Twelve) (guard : d0 pattern = 1) : d826 pattern ≤ (1 : Int) + d826 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17452 (pattern : Twelve) (guard : d1852 pattern = 1) : d840 pattern ≤ (1 : Int) + d826 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17450 pattern childGuard
    simpa only [d1852, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17451 pattern childGuard
    simpa only [d1852, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17453 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11225 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11278 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17454 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17440 pattern childGuard
    simpa only [d36, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d36, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17455 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (1 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17453 pattern childGuard
    simpa only [d827, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17454 pattern childGuard
    simpa only [d827, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17456 (pattern : Twelve) (guard : d1852 pattern = 1) : d841 pattern ≤ (1 : Int) + d825 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17455 pattern childGuard
    simpa only [d1852, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17446 pattern childGuard
    simpa only [d1852, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17457 (pattern : Twelve) (guard : d1852 pattern = 1) : d854 pattern ≤ (1 : Int) + d3185 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d854, d3185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17452 pattern childGuard
    simpa only [d854, d3185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d854, d3185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17456 pattern childGuard
    simpa only [d854, d3185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17458 (pattern : Twelve) (guard : d1852 pattern = 1) : d861 pattern ≤ (1 : Int) + d3186 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d861, d3186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17448 pattern childGuard
    simpa only [d861, d3186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d861, d3186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17457 pattern childGuard
    simpa only [d861, d3186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17459 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17433 pattern childGuard
    simpa only [d30, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d30, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17460 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17334 pattern childGuard
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17459 pattern childGuard
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17461 (pattern : Twelve) (guard : d0 pattern = 1) : d828 pattern ≤ (1 : Int) + d828 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17462 (pattern : Twelve) (guard : d1852 pattern = 1) : d842 pattern ≤ (1 : Int) + d828 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17460 pattern childGuard
    simpa only [d1852, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17461 pattern childGuard
    simpa only [d1852, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17463 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11230 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11233 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17464 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11230 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17463 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17465 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17440 pattern childGuard
    simpa only [d34, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17464 pattern childGuard
    simpa only [d34, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17466 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (1 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17453 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17465 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17467 (pattern : Twelve) (guard : d1852 pattern = 1) : d843 pattern ≤ (1 : Int) + d825 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17466 pattern childGuard
    simpa only [d1852, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17446 pattern childGuard
    simpa only [d1852, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17468 (pattern : Twelve) (guard : d1852 pattern = 1) : d855 pattern ≤ (1 : Int) + d3187 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d855, d3187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17462 pattern childGuard
    simpa only [d855, d3187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d855, d3187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17467 pattern childGuard
    simpa only [d855, d3187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17469 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11138 pattern childGuard
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17470 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (1 : Int) + d820 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17469 pattern childGuard
    simpa only [d39, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d39, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17471 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (1 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17363 pattern childGuard
    simpa only [d59, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17470 pattern childGuard
    simpa only [d59, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17472 (pattern : Twelve) (guard : d0 pattern = 1) : d829 pattern ≤ (1 : Int) + d829 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17473 (pattern : Twelve) (guard : d1852 pattern = 1) : d844 pattern ≤ (1 : Int) + d829 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17471 pattern childGuard
    simpa only [d1852, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17472 pattern childGuard
    simpa only [d1852, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17474 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (1 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12341 pattern childGuard
    simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12584 pattern childGuard
    simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17475 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11278 pattern childGuard
    simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17474 pattern childGuard
    simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17476 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11274 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11230 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17477 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (1 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17364 pattern childGuard
    simpa only [d9, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11233 pattern childGuard
    simpa only [d9, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17478 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (1 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17476 pattern childGuard
    simpa only [d23, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17477 pattern childGuard
    simpa only [d23, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17479 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17478 pattern childGuard
    simpa only [d40, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d40, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17480 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (1 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17475 pattern childGuard
    simpa only [d830, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17479 pattern childGuard
    simpa only [d830, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17481 (pattern : Twelve) (guard : d0 pattern = 1) : d831 pattern ≤ (1 : Int) + d831 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17482 (pattern : Twelve) (guard : d1852 pattern = 1) : d845 pattern ≤ (1 : Int) + d831 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17480 pattern childGuard
    simpa only [d1852, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17481 pattern childGuard
    simpa only [d1852, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17483 (pattern : Twelve) (guard : d1852 pattern = 1) : d856 pattern ≤ (1 : Int) + d3188 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d856, d3188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17473 pattern childGuard
    simpa only [d856, d3188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d856, d3188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17482 pattern childGuard
    simpa only [d856, d3188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17484 (pattern : Twelve) (guard : d1852 pattern = 1) : d862 pattern ≤ (1 : Int) + d3189 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d862, d3189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17468 pattern childGuard
    simpa only [d862, d3189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d862, d3189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17483 pattern childGuard
    simpa only [d862, d3189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17485 (pattern : Twelve) (guard : d1852 pattern = 1) : d863 pattern ≤ (1 : Int) + d3190 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d863, d3190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17457 pattern childGuard
    simpa only [d863, d3190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d863, d3190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17373 pattern childGuard
    simpa only [d863, d3190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17486 (pattern : Twelve) (guard : d1852 pattern = 1) : d867 pattern ≤ (1 : Int) + d3191 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d867, d3191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17484 pattern childGuard
    simpa only [d867, d3191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d867, d3191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17485 pattern childGuard
    simpa only [d867, d3191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17487 (pattern : Twelve) (guard : d1852 pattern = 1) : d869 pattern ≤ (1 : Int) + d3192 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d869, d3192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17458 pattern childGuard
    simpa only [d869, d3192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d869, d3192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17486 pattern childGuard
    simpa only [d869, d3192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17488 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11060 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17318 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17489 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d874 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17488 pattern childGuard
    simpa only [d874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17490 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d875 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17433 pattern childGuard
    simpa only [d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17488 pattern childGuard
    simpa only [d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17491 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d882 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17489 pattern childGuard
    simpa only [d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17490 pattern childGuard
    simpa only [d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17492 (pattern : Twelve) (guard : d0 pattern = 1) : d882 pattern ≤ (1 : Int) + d882 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17493 (pattern : Twelve) (guard : d1852 pattern = 1) : d890 pattern ≤ (1 : Int) + d882 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17491 pattern childGuard
    simpa only [d1852, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17492 pattern childGuard
    simpa only [d1852, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17494 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17377 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11403 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17495 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (1 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17379 pattern childGuard
    simpa only [d7, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11405 pattern childGuard
    simpa only [d7, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17496 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17494 pattern childGuard
    simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17495 pattern childGuard
    simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17497 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d876 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11225 pattern childGuard
    simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17496 pattern childGuard
    simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17498 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17497 pattern childGuard
    simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17444 pattern childGuard
    simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17499 (pattern : Twelve) (guard : d0 pattern = 1) : d883 pattern ≤ (1 : Int) + d883 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban21.Diagram
