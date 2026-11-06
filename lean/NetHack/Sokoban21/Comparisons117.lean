/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons116
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c16380 (pattern : Twelve) (guard : d0 pattern = 1) : d13 pattern ≤ (1 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16381 (pattern : Twelve) (guard : d2746 pattern = 1) : d20 pattern ≤ (1 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16379 pattern childGuard
    simpa only [d2746, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16380 pattern childGuard
    simpa only [d2746, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16382 (pattern : Twelve) (guard : d2746 pattern = 1) : d31 pattern ≤ (1 : Int) + d2635 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d31, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15933 pattern childGuard
    simpa only [d31, d2635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d31, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16381 pattern childGuard
    simpa only [d31, d2635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16383 (pattern : Twelve) (guard : d2746 pattern = 1) : d52 pattern ≤ (1 : Int) + d2636 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d52, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16378 pattern childGuard
    simpa only [d52, d2636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d52, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16382 pattern childGuard
    simpa only [d52, d2636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16384 (pattern : Twelve) (guard : d7 pattern = 1) : d13 pattern ≤ (1 : Int) + d5 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16266 pattern childGuard
    simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11197 pattern childGuard
    simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16385 (pattern : Twelve) (guard : d0 pattern = 1) : d14 pattern ≤ (1 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16386 (pattern : Twelve) (guard : d2746 pattern = 1) : d21 pattern ≤ (1 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16384 pattern childGuard
    simpa only [d2746, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16385 pattern childGuard
    simpa only [d2746, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16387 (pattern : Twelve) (guard : d2746 pattern = 1) : d32 pattern ≤ (1 : Int) + d2898 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d32, d2898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16363 pattern childGuard
    simpa only [d32, d2898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d32, d2898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16386 pattern childGuard
    simpa only [d32, d2898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16388 (pattern : Twelve) (guard : d2746 pattern = 1) : d53 pattern ≤ (1 : Int) + d2899 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d53, d2899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16378 pattern childGuard
    simpa only [d53, d2899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d53, d2899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16387 pattern childGuard
    simpa only [d53, d2899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16389 (pattern : Twelve) (guard : d2746 pattern = 1) : d74 pattern ≤ (1 : Int) + d2900 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d74, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16383 pattern childGuard
    simpa only [d74, d2900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d74, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16388 pattern childGuard
    simpa only [d74, d2900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16390 (pattern : Twelve) (guard : d2746 pattern = 1) : d33 pattern ≤ (1 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15933 pattern childGuard
    simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15986 pattern childGuard
    simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16391 (pattern : Twelve) (guard : d2746 pattern = 1) : d54 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16378 pattern childGuard
    simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16390 pattern childGuard
    simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16392 (pattern : Twelve) (guard : d2746 pattern = 1) : d23 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15966 pattern childGuard
    simpa only [d2746, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16368 pattern childGuard
    simpa only [d2746, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16393 (pattern : Twelve) (guard : d2746 pattern = 1) : d34 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d34, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16363 pattern childGuard
    simpa only [d34, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d34, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16392 pattern childGuard
    simpa only [d34, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16394 (pattern : Twelve) (guard : d2746 pattern = 1) : d55 pattern ≤ (1 : Int) + d65 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d55, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16393 pattern childGuard
    simpa only [d55, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d55, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16374 pattern childGuard
    simpa only [d55, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16395 (pattern : Twelve) (guard : d2746 pattern = 1) : d75 pattern ≤ (1 : Int) + d85 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d75, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16391 pattern childGuard
    simpa only [d75, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d75, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16394 pattern childGuard
    simpa only [d75, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16396 (pattern : Twelve) (guard : d2746 pattern = 1) : d92 pattern ≤ (1 : Int) + d2901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d92, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16389 pattern childGuard
    simpa only [d92, d2901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d92, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16395 pattern childGuard
    simpa only [d92, d2901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16397 (pattern : Twelve) (guard : d2746 pattern = 1) : d102 pattern ≤ (1 : Int) + d2902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d102, d2902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16377 pattern childGuard
    simpa only [d102, d2902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d102, d2902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16396 pattern childGuard
    simpa only [d102, d2902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16398 (pattern : Twelve) (guard : d2746 pattern = 1) : d76 pattern ≤ (1 : Int) + d2896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d76, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15933 pattern childGuard
    simpa only [d76, d2896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d76, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16394 pattern childGuard
    simpa only [d76, d2896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16399 (pattern : Twelve) (guard : d2746 pattern = 1) : d93 pattern ≤ (1 : Int) + d2897 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d93, d2897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16367 pattern childGuard
    simpa only [d93, d2897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d93, d2897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16398 pattern childGuard
    simpa only [d93, d2897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16400 (pattern : Twelve) (guard : d2746 pattern = 1) : d56 pattern ≤ (1 : Int) + d56 pattern := by
  omega
theorem c16401 (pattern : Twelve) (guard : d2746 pattern = 1) : d36 pattern ≤ (1 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d36, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16363 pattern childGuard
    simpa only [d36, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d36, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d36, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16402 (pattern : Twelve) (guard : d2746 pattern = 1) : d57 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d57, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16378 pattern childGuard
    simpa only [d57, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d57, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16401 pattern childGuard
    simpa only [d57, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16403 (pattern : Twelve) (guard : d2746 pattern = 1) : d77 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16400 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16402 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16404 (pattern : Twelve) (guard : d2746 pattern = 1) : d78 pattern ≤ (1 : Int) + d85 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d78, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16400 pattern childGuard
    simpa only [d78, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d78, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16394 pattern childGuard
    simpa only [d78, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16405 (pattern : Twelve) (guard : d2746 pattern = 1) : d94 pattern ≤ (1 : Int) + d2903 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d94, d2903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16403 pattern childGuard
    simpa only [d94, d2903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d94, d2903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16404 pattern childGuard
    simpa only [d94, d2903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16406 (pattern : Twelve) (guard : d2746 pattern = 1) : d103 pattern ≤ (1 : Int) + d2904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d103, d2904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16399 pattern childGuard
    simpa only [d103, d2904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d103, d2904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16405 pattern childGuard
    simpa only [d103, d2904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16407 (pattern : Twelve) (guard : d2746 pattern = 1) : d110 pattern ≤ (1 : Int) + d2905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d110, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16397 pattern childGuard
    simpa only [d110, d2905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d110, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16406 pattern childGuard
    simpa only [d110, d2905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16408 (pattern : Twelve) (guard : d2746 pattern = 1) : d3 pattern ≤ (1 : Int) + d3 pattern := by
  omega
theorem c16409 (pattern : Twelve) (guard : d2746 pattern = 1) : d37 pattern ≤ (1 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d37, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16363 pattern childGuard
    simpa only [d37, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d37, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16408 pattern childGuard
    simpa only [d37, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16410 (pattern : Twelve) (guard : d2746 pattern = 1) : d58 pattern ≤ (1 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d58, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16378 pattern childGuard
    simpa only [d58, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d58, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16409 pattern childGuard
    simpa only [d58, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16411 (pattern : Twelve) (guard : d2746 pattern = 1) : d79 pattern ≤ (1 : Int) + d2614 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d79, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16378 pattern childGuard
    simpa only [d79, d2614, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d79, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16410 pattern childGuard
    simpa only [d79, d2614, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16412 (pattern : Twelve) (guard : d2746 pattern = 1) : d80 pattern ≤ (1 : Int) + d2906 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d80, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16378 pattern childGuard
    simpa only [d80, d2906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d80, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16394 pattern childGuard
    simpa only [d80, d2906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16413 (pattern : Twelve) (guard : d2746 pattern = 1) : d95 pattern ≤ (1 : Int) + d2907 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d95, d2907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16411 pattern childGuard
    simpa only [d95, d2907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d95, d2907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16412 pattern childGuard
    simpa only [d95, d2907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16414 (pattern : Twelve) (guard : d2746 pattern = 1) : d59 pattern ≤ (1 : Int) + d59 pattern := by
  omega
theorem c16415 (pattern : Twelve) (guard : d2746 pattern = 1) : d38 pattern ≤ (1 : Int) + d38 pattern := by
  omega
theorem c16416 (pattern : Twelve) (guard : d2746 pattern = 1) : d40 pattern ≤ (1 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d40, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16392 pattern childGuard
    simpa only [d40, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d40, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d40, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16417 (pattern : Twelve) (guard : d2746 pattern = 1) : d60 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d60, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16415 pattern childGuard
    simpa only [d60, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d60, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16416 pattern childGuard
    simpa only [d60, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16418 (pattern : Twelve) (guard : d2746 pattern = 1) : d81 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16414 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16417 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16419 (pattern : Twelve) (guard : d0 pattern = 1) : d15 pattern ≤ (1 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16420 (pattern : Twelve) (guard : d2746 pattern = 1) : d24 pattern ≤ (1 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16033 pattern childGuard
    simpa only [d2746, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16419 pattern childGuard
    simpa only [d2746, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16421 (pattern : Twelve) (guard : d2746 pattern = 1) : d41 pattern ≤ (1 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d41, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16392 pattern childGuard
    simpa only [d41, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d41, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16420 pattern childGuard
    simpa only [d41, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16422 (pattern : Twelve) (guard : d7 pattern = 1) : d16 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16177 pattern childGuard
    simpa only [d7, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11184 pattern childGuard
    simpa only [d7, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16423 (pattern : Twelve) (guard : d0 pattern = 1) : d12 pattern ≤ (1 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16424 (pattern : Twelve) (guard : d2746 pattern = 1) : d25 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16422 pattern childGuard
    simpa only [d2746, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16423 pattern childGuard
    simpa only [d2746, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16425 (pattern : Twelve) (guard : d2746 pattern = 1) : d42 pattern ≤ (1 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d42, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16424 pattern childGuard
    simpa only [d42, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d42, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d42, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16426 (pattern : Twelve) (guard : d2746 pattern = 1) : d61 pattern ≤ (1 : Int) + d69 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d61, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16421 pattern childGuard
    simpa only [d61, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d61, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16425 pattern childGuard
    simpa only [d61, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16427 (pattern : Twelve) (guard : d2746 pattern = 1) : d82 pattern ≤ (1 : Int) + d89 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d82, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16414 pattern childGuard
    simpa only [d82, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d82, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16426 pattern childGuard
    simpa only [d82, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16428 (pattern : Twelve) (guard : d2746 pattern = 1) : d96 pattern ≤ (1 : Int) + d2908 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d96, d2908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16418 pattern childGuard
    simpa only [d96, d2908, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d96, d2908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16427 pattern childGuard
    simpa only [d96, d2908, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16429 (pattern : Twelve) (guard : d2746 pattern = 1) : d104 pattern ≤ (1 : Int) + d2909 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d104, d2909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16413 pattern childGuard
    simpa only [d104, d2909, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d104, d2909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16428 pattern childGuard
    simpa only [d104, d2909, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16430 (pattern : Twelve) (guard : d2746 pattern = 1) : d105 pattern ≤ (1 : Int) + d2910 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d105, d2910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16405 pattern childGuard
    simpa only [d105, d2910, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d105, d2910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d105, d2910, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16431 (pattern : Twelve) (guard : d2746 pattern = 1) : d111 pattern ≤ (1 : Int) + d2911 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d111, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16429 pattern childGuard
    simpa only [d111, d2911, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d111, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16430 pattern childGuard
    simpa only [d111, d2911, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16432 (pattern : Twelve) (guard : d2746 pattern = 1) : d114 pattern ≤ (1 : Int) + d2912 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d114, d2912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16407 pattern childGuard
    simpa only [d114, d2912, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d114, d2912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16431 pattern childGuard
    simpa only [d114, d2912, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16433 (pattern : Twelve) (guard : d2746 pattern = 1) : d120 pattern ≤ (1 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d120, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16363 pattern childGuard
    simpa only [d120, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d120, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16424 pattern childGuard
    simpa only [d120, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16434 (pattern : Twelve) (guard : d2746 pattern = 1) : d129 pattern ≤ (1 : Int) + d2913 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d129, d2913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16433 pattern childGuard
    simpa only [d129, d2913, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d129, d2913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16374 pattern childGuard
    simpa only [d129, d2913, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16435 (pattern : Twelve) (guard : d2746 pattern = 1) : d136 pattern ≤ (1 : Int) + d2914 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d136, d2914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15933 pattern childGuard
    simpa only [d136, d2914, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d136, d2914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16434 pattern childGuard
    simpa only [d136, d2914, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16436 (pattern : Twelve) (guard : d2746 pattern = 1) : d144 pattern ≤ (1 : Int) + d2915 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d144, d2915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16367 pattern childGuard
    simpa only [d144, d2915, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d144, d2915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16435 pattern childGuard
    simpa only [d144, d2915, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16437 (pattern : Twelve) (guard : d2746 pattern = 1) : d121 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d121, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15933 pattern childGuard
    simpa only [d121, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d121, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16392 pattern childGuard
    simpa only [d121, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16438 (pattern : Twelve) (guard : d2746 pattern = 1) : d130 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d130, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16437 pattern childGuard
    simpa only [d130, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d130, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16401 pattern childGuard
    simpa only [d130, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16439 (pattern : Twelve) (guard : d2746 pattern = 1) : d137 pattern ≤ (1 : Int) + d2916 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d137, d2916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16383 pattern childGuard
    simpa only [d137, d2916, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d137, d2916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16438 pattern childGuard
    simpa only [d137, d2916, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16440 (pattern : Twelve) (guard : d2746 pattern = 1) : d138 pattern ≤ (1 : Int) + d2917 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d138, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16400 pattern childGuard
    simpa only [d138, d2917, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d138, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16434 pattern childGuard
    simpa only [d138, d2917, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16441 (pattern : Twelve) (guard : d2746 pattern = 1) : d145 pattern ≤ (1 : Int) + d2918 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d145, d2918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16439 pattern childGuard
    simpa only [d145, d2918, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d145, d2918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16440 pattern childGuard
    simpa only [d145, d2918, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16442 (pattern : Twelve) (guard : d2746 pattern = 1) : d149 pattern ≤ (1 : Int) + d2919 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d149, d2919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16436 pattern childGuard
    simpa only [d149, d2919, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d149, d2919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16441 pattern childGuard
    simpa only [d149, d2919, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16443 (pattern : Twelve) (guard : d2746 pattern = 1) : d139 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16400 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16438 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16444 (pattern : Twelve) (guard : d2746 pattern = 1) : d146 pattern ≤ (1 : Int) + d2920 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d146, d2920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16443 pattern childGuard
    simpa only [d146, d2920, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d146, d2920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16440 pattern childGuard
    simpa only [d146, d2920, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16445 (pattern : Twelve) (guard : d2746 pattern = 1) : d150 pattern ≤ (1 : Int) + d2921 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d150, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16436 pattern childGuard
    simpa only [d150, d2921, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d150, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16444 pattern childGuard
    simpa only [d150, d2921, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16446 (pattern : Twelve) (guard : d2746 pattern = 1) : d153 pattern ≤ (1 : Int) + d2922 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d153, d2922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16442 pattern childGuard
    simpa only [d153, d2922, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d153, d2922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16445 pattern childGuard
    simpa only [d153, d2922, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16447 (pattern : Twelve) (guard : d2746 pattern = 1) : d4 pattern ≤ (1 : Int) + d4 pattern := by
  omega
theorem c16448 (pattern : Twelve) (guard : d2746 pattern = 1) : d122 pattern ≤ (1 : Int) + d2635 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d122, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16363 pattern childGuard
    simpa only [d122, d2635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d122, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16447 pattern childGuard
    simpa only [d122, d2635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16449 (pattern : Twelve) (guard : d2746 pattern = 1) : d131 pattern ≤ (1 : Int) + d2636 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d131, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16437 pattern childGuard
    simpa only [d131, d2636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d131, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16448 pattern childGuard
    simpa only [d131, d2636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16450 (pattern : Twelve) (guard : d2746 pattern = 1) : d140 pattern ≤ (1 : Int) + d2637 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d140, d2637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16378 pattern childGuard
    simpa only [d140, d2637, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d140, d2637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16449 pattern childGuard
    simpa only [d140, d2637, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16451 (pattern : Twelve) (guard : d2746 pattern = 1) : d132 pattern ≤ (1 : Int) + d132 pattern := by
  omega
theorem c16452 (pattern : Twelve) (guard : d2746 pattern = 1) : d141 pattern ≤ (1 : Int) + d2923 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d141, d2923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16451 pattern childGuard
    simpa only [d141, d2923, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d141, d2923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16434 pattern childGuard
    simpa only [d141, d2923, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16453 (pattern : Twelve) (guard : d2746 pattern = 1) : d147 pattern ≤ (1 : Int) + d2924 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d147, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16450 pattern childGuard
    simpa only [d147, d2924, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d147, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16452 pattern childGuard
    simpa only [d147, d2924, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16454 (pattern : Twelve) (guard : d2746 pattern = 1) : d2 pattern ≤ (1 : Int) + d2 pattern := by
  omega
theorem c16455 (pattern : Twelve) (guard : d2746 pattern = 1) : d118 pattern ≤ (1 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16122 pattern childGuard
    simpa only [d2746, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16385 pattern childGuard
    simpa only [d2746, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16456 (pattern : Twelve) (guard : d2746 pattern = 1) : d124 pattern ≤ (1 : Int) + d126 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d124, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16454 pattern childGuard
    simpa only [d124, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d124, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16455 pattern childGuard
    simpa only [d124, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16457 (pattern : Twelve) (guard : d0 pattern = 1) : d117 pattern ≤ (1 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16458 (pattern : Twelve) (guard : d2746 pattern = 1) : d119 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16024 pattern childGuard
    simpa only [d2746, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16457 pattern childGuard
    simpa only [d2746, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16459 (pattern : Twelve) (guard : d2746 pattern = 1) : d125 pattern ≤ (1 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d125, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16458 pattern childGuard
    simpa only [d125, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d125, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d125, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16460 (pattern : Twelve) (guard : d2746 pattern = 1) : d133 pattern ≤ (1 : Int) + d134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d133, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16456 pattern childGuard
    simpa only [d133, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d133, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16459 pattern childGuard
    simpa only [d133, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16461 (pattern : Twelve) (guard : d2746 pattern = 1) : d142 pattern ≤ (1 : Int) + d2640 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d142, d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16414 pattern childGuard
    simpa only [d142, d2640, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d142, d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16460 pattern childGuard
    simpa only [d142, d2640, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16462 (pattern : Twelve) (guard : d2746 pattern = 1) : d134 pattern ≤ (1 : Int) + d134 pattern := by
  omega
theorem c16463 (pattern : Twelve) (guard : d2746 pattern = 1) : d127 pattern ≤ (1 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d127, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16392 pattern childGuard
    simpa only [d127, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d127, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15986 pattern childGuard
    simpa only [d127, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16464 (pattern : Twelve) (guard : d2746 pattern = 1) : d128 pattern ≤ (1 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d128, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16381 pattern childGuard
    simpa only [d128, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d128, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d128, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16465 (pattern : Twelve) (guard : d2746 pattern = 1) : d135 pattern ≤ (1 : Int) + d2925 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d135, d2925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16463 pattern childGuard
    simpa only [d135, d2925, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d135, d2925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16464 pattern childGuard
    simpa only [d135, d2925, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16466 (pattern : Twelve) (guard : d2746 pattern = 1) : d143 pattern ≤ (1 : Int) + d2926 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d143, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16462 pattern childGuard
    simpa only [d143, d2926, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d143, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16465 pattern childGuard
    simpa only [d143, d2926, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16467 (pattern : Twelve) (guard : d2746 pattern = 1) : d148 pattern ≤ (1 : Int) + d2927 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d148, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16461 pattern childGuard
    simpa only [d148, d2927, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d148, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16466 pattern childGuard
    simpa only [d148, d2927, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16468 (pattern : Twelve) (guard : d2746 pattern = 1) : d151 pattern ≤ (1 : Int) + d2928 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d151, d2928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16453 pattern childGuard
    simpa only [d151, d2928, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d151, d2928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16467 pattern childGuard
    simpa only [d151, d2928, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16469 (pattern : Twelve) (guard : d2746 pattern = 1) : d152 pattern ≤ (1 : Int) + d2929 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d152, d2929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16444 pattern childGuard
    simpa only [d152, d2929, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d152, d2929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d152, d2929, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16470 (pattern : Twelve) (guard : d2746 pattern = 1) : d154 pattern ≤ (1 : Int) + d2930 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d154, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16468 pattern childGuard
    simpa only [d154, d2930, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d154, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16469 pattern childGuard
    simpa only [d154, d2930, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16471 (pattern : Twelve) (guard : d2746 pattern = 1) : d155 pattern ≤ (1 : Int) + d2931 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d155, d2931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16446 pattern childGuard
    simpa only [d155, d2931, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d155, d2931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16470 pattern childGuard
    simpa only [d155, d2931, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16472 (pattern : Twelve) (guard : d2746 pattern = 1) : d156 pattern ≤ (1 : Int) + d2932 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d156, d2932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16432 pattern childGuard
    simpa only [d156, d2932, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d156, d2932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16471 pattern childGuard
    simpa only [d156, d2932, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16473 (pattern : Twelve) (guard : d2746 pattern = 1) : d814 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16138 pattern childGuard
    simpa only [d2746, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12785 pattern childGuard
    simpa only [d2746, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16474 (pattern : Twelve) (guard : d2746 pattern = 1) : d816 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16473 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16364 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16475 (pattern : Twelve) (guard : d2746 pattern = 1) : d824 pattern ≤ (1 : Int) + d2933 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d824, d2933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16365 pattern childGuard
    simpa only [d824, d2933, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d824, d2933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16474 pattern childGuard
    simpa only [d824, d2933, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16476 (pattern : Twelve) (guard : d2746 pattern = 1) : d838 pattern ≤ (1 : Int) + d2934 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d838, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15933 pattern childGuard
    simpa only [d838, d2934, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d838, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16475 pattern childGuard
    simpa only [d838, d2934, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16477 (pattern : Twelve) (guard : d2746 pattern = 1) : d817 pattern ≤ (1 : Int) + d46 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d817, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16373 pattern childGuard
    simpa only [d817, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d817, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16424 pattern childGuard
    simpa only [d817, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16478 (pattern : Twelve) (guard : d2746 pattern = 1) : d825 pattern ≤ (1 : Int) + d2935 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d825, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16477 pattern childGuard
    simpa only [d825, d2935, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d825, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16425 pattern childGuard
    simpa only [d825, d2935, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16479 (pattern : Twelve) (guard : d2746 pattern = 1) : d839 pattern ≤ (1 : Int) + d2936 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d839, d2936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16363 pattern childGuard
    simpa only [d839, d2936, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d839, d2936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16478 pattern childGuard
    simpa only [d839, d2936, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16480 (pattern : Twelve) (guard : d2746 pattern = 1) : d853 pattern ≤ (1 : Int) + d2937 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d853, d2937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16476 pattern childGuard
    simpa only [d853, d2937, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d853, d2937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16479 pattern childGuard
    simpa only [d853, d2937, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16481 (pattern : Twelve) (guard : d2746 pattern = 1) : d818 pattern ≤ (1 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d818, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16473 pattern childGuard
    simpa only [d818, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d818, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d818, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16482 (pattern : Twelve) (guard : d2746 pattern = 1) : d826 pattern ≤ (1 : Int) + d65 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d826, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16393 pattern childGuard
    simpa only [d826, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d826, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16481 pattern childGuard
    simpa only [d826, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16483 (pattern : Twelve) (guard : d2746 pattern = 1) : d840 pattern ≤ (1 : Int) + d85 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d840, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16400 pattern childGuard
    simpa only [d840, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d840, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16482 pattern childGuard
    simpa only [d840, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16484 (pattern : Twelve) (guard : d2746 pattern = 1) : d827 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d827, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16393 pattern childGuard
    simpa only [d827, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d827, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16401 pattern childGuard
    simpa only [d827, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16485 (pattern : Twelve) (guard : d2746 pattern = 1) : d841 pattern ≤ (1 : Int) + d2938 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d841, d2938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16484 pattern childGuard
    simpa only [d841, d2938, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d841, d2938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16478 pattern childGuard
    simpa only [d841, d2938, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16486 (pattern : Twelve) (guard : d2746 pattern = 1) : d854 pattern ≤ (1 : Int) + d2939 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d854, d2939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16483 pattern childGuard
    simpa only [d854, d2939, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d854, d2939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16485 pattern childGuard
    simpa only [d854, d2939, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16487 (pattern : Twelve) (guard : d2746 pattern = 1) : d861 pattern ≤ (1 : Int) + d2940 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d861, d2940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16480 pattern childGuard
    simpa only [d861, d2940, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d861, d2940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16486 pattern childGuard
    simpa only [d861, d2940, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16488 (pattern : Twelve) (guard : d2746 pattern = 1) : d819 pattern ≤ (1 : Int) + d46 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d819, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16473 pattern childGuard
    simpa only [d819, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d819, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16408 pattern childGuard
    simpa only [d819, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16489 (pattern : Twelve) (guard : d2746 pattern = 1) : d828 pattern ≤ (1 : Int) + d67 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d828, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16393 pattern childGuard
    simpa only [d828, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d828, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16488 pattern childGuard
    simpa only [d828, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16490 (pattern : Twelve) (guard : d2746 pattern = 1) : d842 pattern ≤ (1 : Int) + d87 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d842, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16378 pattern childGuard
    simpa only [d842, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d842, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16489 pattern childGuard
    simpa only [d842, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16491 (pattern : Twelve) (guard : d2746 pattern = 1) : d843 pattern ≤ (1 : Int) + d2941 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d843, d2941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16393 pattern childGuard
    simpa only [d843, d2941, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d843, d2941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16478 pattern childGuard
    simpa only [d843, d2941, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16492 (pattern : Twelve) (guard : d2746 pattern = 1) : d855 pattern ≤ (1 : Int) + d2942 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d855, d2942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16490 pattern childGuard
    simpa only [d855, d2942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d855, d2942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16491 pattern childGuard
    simpa only [d855, d2942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16493 (pattern : Twelve) (guard : d2746 pattern = 1) : d815 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16178 pattern childGuard
    simpa only [d2746, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12806 pattern childGuard
    simpa only [d2746, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16494 (pattern : Twelve) (guard : d2746 pattern = 1) : d820 pattern ≤ (1 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d820, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16493 pattern childGuard
    simpa only [d820, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d820, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d820, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16495 (pattern : Twelve) (guard : d2746 pattern = 1) : d829 pattern ≤ (1 : Int) + d69 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d829, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16421 pattern childGuard
    simpa only [d829, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d829, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16494 pattern childGuard
    simpa only [d829, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16496 (pattern : Twelve) (guard : d2746 pattern = 1) : d844 pattern ≤ (1 : Int) + d89 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d844, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16414 pattern childGuard
    simpa only [d844, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d844, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16495 pattern childGuard
    simpa only [d844, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16497 (pattern : Twelve) (guard : d2746 pattern = 1) : d830 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d830, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16421 pattern childGuard
    simpa only [d830, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d830, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16416 pattern childGuard
    simpa only [d830, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16498 (pattern : Twelve) (guard : d2746 pattern = 1) : d821 pattern ≤ (1 : Int) + d780 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d821, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16424 pattern childGuard
    simpa only [d821, d780, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d821, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16386 pattern childGuard
    simpa only [d821, d780, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16499 (pattern : Twelve) (guard : d2746 pattern = 1) : d822 pattern ≤ (1 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d822, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16386 pattern childGuard
    simpa only [d822, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d822, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d822, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16500 (pattern : Twelve) (guard : d2746 pattern = 1) : d831 pattern ≤ (1 : Int) + d2943 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d831, d2943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16498 pattern childGuard
    simpa only [d831, d2943, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d831, d2943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16499 pattern childGuard
    simpa only [d831, d2943, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16501 (pattern : Twelve) (guard : d2746 pattern = 1) : d845 pattern ≤ (1 : Int) + d2944 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d845, d2944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16497 pattern childGuard
    simpa only [d845, d2944, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d845, d2944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16500 pattern childGuard
    simpa only [d845, d2944, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16502 (pattern : Twelve) (guard : d2746 pattern = 1) : d856 pattern ≤ (1 : Int) + d2945 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d856, d2945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16496 pattern childGuard
    simpa only [d856, d2945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d856, d2945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16501 pattern childGuard
    simpa only [d856, d2945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16503 (pattern : Twelve) (guard : d2746 pattern = 1) : d862 pattern ≤ (1 : Int) + d2946 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d862, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16492 pattern childGuard
    simpa only [d862, d2946, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d862, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16502 pattern childGuard
    simpa only [d862, d2946, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16504 (pattern : Twelve) (guard : d2746 pattern = 1) : d863 pattern ≤ (1 : Int) + d2947 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d863, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16486 pattern childGuard
    simpa only [d863, d2947, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d863, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d863, d2947, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16505 (pattern : Twelve) (guard : d2746 pattern = 1) : d867 pattern ≤ (1 : Int) + d2948 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d867, d2948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16503 pattern childGuard
    simpa only [d867, d2948, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d867, d2948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16504 pattern childGuard
    simpa only [d867, d2948, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16506 (pattern : Twelve) (guard : d2746 pattern = 1) : d869 pattern ≤ (1 : Int) + d2949 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d869, d2949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16487 pattern childGuard
    simpa only [d869, d2949, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d869, d2949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16505 pattern childGuard
    simpa only [d869, d2949, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16507 (pattern : Twelve) (guard : d0 pattern = 1) : d8 pattern ≤ (1 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16508 (pattern : Twelve) (guard : d2746 pattern = 1) : d872 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15940 pattern childGuard
    simpa only [d2746, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16507 pattern childGuard
    simpa only [d2746, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16509 (pattern : Twelve) (guard : d2746 pattern = 1) : d874 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d874, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16363 pattern childGuard
    simpa only [d874, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d874, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16508 pattern childGuard
    simpa only [d874, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16510 (pattern : Twelve) (guard : d2746 pattern = 1) : d875 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16473 pattern childGuard
    simpa only [d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16508 pattern childGuard
    simpa only [d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16511 (pattern : Twelve) (guard : d2746 pattern = 1) : d882 pattern ≤ (1 : Int) + d2933 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d882, d2933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16509 pattern childGuard
    simpa only [d882, d2933, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d882, d2933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16510 pattern childGuard
    simpa only [d882, d2933, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16512 (pattern : Twelve) (guard : d2746 pattern = 1) : d890 pattern ≤ (1 : Int) + d2934 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d890, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15933 pattern childGuard
    simpa only [d890, d2934, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d890, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16511 pattern childGuard
    simpa only [d890, d2934, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16513 (pattern : Twelve) (guard : d2746 pattern = 1) : d876 pattern ≤ (1 : Int) + d2950 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d876, d2950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16373 pattern childGuard
    simpa only [d876, d2950, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d876, d2950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16386 pattern childGuard
    simpa only [d876, d2950, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16514 (pattern : Twelve) (guard : d2746 pattern = 1) : d883 pattern ≤ (1 : Int) + d2951 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d883, d2951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16513 pattern childGuard
    simpa only [d883, d2951, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d883, d2951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16425 pattern childGuard
    simpa only [d883, d2951, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16515 (pattern : Twelve) (guard : d2746 pattern = 1) : d891 pattern ≤ (1 : Int) + d2952 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d891, d2952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16363 pattern childGuard
    simpa only [d891, d2952, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d891, d2952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16514 pattern childGuard
    simpa only [d891, d2952, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16516 (pattern : Twelve) (guard : d2746 pattern = 1) : d898 pattern ≤ (1 : Int) + d2953 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d898, d2953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16512 pattern childGuard
    simpa only [d898, d2953, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d898, d2953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16515 pattern childGuard
    simpa only [d898, d2953, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16517 (pattern : Twelve) (guard : d2746 pattern = 1) : d877 pattern ≤ (1 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d877, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16363 pattern childGuard
    simpa only [d877, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d877, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16493 pattern childGuard
    simpa only [d877, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16518 (pattern : Twelve) (guard : d2746 pattern = 1) : d884 pattern ≤ (1 : Int) + d2913 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d884, d2913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16517 pattern childGuard
    simpa only [d884, d2913, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d884, d2913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16481 pattern childGuard
    simpa only [d884, d2913, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16519 (pattern : Twelve) (guard : d2746 pattern = 1) : d892 pattern ≤ (1 : Int) + d2917 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d892, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16400 pattern childGuard
    simpa only [d892, d2917, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d892, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16518 pattern childGuard
    simpa only [d892, d2917, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
