/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons109
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c15400 (pattern : Twelve) (guard : d2496 pattern = 1) : d1674 pattern ≤ (1 : Int) + d2526 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1674, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15399 pattern childGuard
    simpa only [d1674, d2526, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1674, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15380 pattern childGuard
    simpa only [d1674, d2526, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15401 (pattern : Twelve) (guard : d0 pattern = 1) : d817 pattern ≤ (1 : Int) + d1289 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15402 (pattern : Twelve) (guard : d1 pattern = 1) : d1665 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1665, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15371 pattern childGuard
    simpa only [d1665, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1665, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11431 pattern childGuard
    simpa only [d1665, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15403 (pattern : Twelve) (guard : d1 pattern = 1) : d1666 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15376 pattern childGuard
    simpa only [d1666, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15402 pattern childGuard
    simpa only [d1666, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15404 (pattern : Twelve) (guard : d1859 pattern = 1) : d1669 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15401 pattern childGuard
    simpa only [d1859, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15403 pattern childGuard
    simpa only [d1859, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15405 (pattern : Twelve) (guard : d2496 pattern = 1) : d1672 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15404 pattern childGuard
    simpa only [d2496, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15334 pattern childGuard
    simpa only [d2496, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15406 (pattern : Twelve) (guard : d0 pattern = 1) : d1289 pattern ≤ (1 : Int) + d1252 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15407 (pattern : Twelve) (guard : d1 pattern = 1) : d183 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11431 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15408 (pattern : Twelve) (guard : d1 pattern = 1) : d1667 pattern ≤ (1 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1667, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15388 pattern childGuard
    simpa only [d1667, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1667, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15407 pattern childGuard
    simpa only [d1667, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15409 (pattern : Twelve) (guard : d1859 pattern = 1) : d1670 pattern ≤ (1 : Int) + d1252 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15406 pattern childGuard
    simpa only [d1859, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15408 pattern childGuard
    simpa only [d1859, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15410 (pattern : Twelve) (guard : d0 pattern = 1) : d1626 pattern ≤ (1 : Int) + d1252 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15411 (pattern : Twelve) (guard : d2496 pattern = 1) : d1673 pattern ≤ (1 : Int) + d1252 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15409 pattern childGuard
    simpa only [d2496, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15410 pattern childGuard
    simpa only [d2496, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15412 (pattern : Twelve) (guard : d2496 pattern = 1) : d1675 pattern ≤ (1 : Int) + d2531 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1675, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15405 pattern childGuard
    simpa only [d1675, d2531, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1675, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15411 pattern childGuard
    simpa only [d1675, d2531, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15413 (pattern : Twelve) (guard : d2496 pattern = 1) : d1676 pattern ≤ (1 : Int) + d2532 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1676, d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15412 pattern childGuard
    simpa only [d1676, d2532, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1676, d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15394 pattern childGuard
    simpa only [d1676, d2532, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15414 (pattern : Twelve) (guard : d2496 pattern = 1) : d1677 pattern ≤ (1 : Int) + d2533 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1677, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15400 pattern childGuard
    simpa only [d1677, d2533, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1677, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15413 pattern childGuard
    simpa only [d1677, d2533, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15415 (pattern : Twelve) (guard : d2496 pattern = 1) : d1678 pattern ≤ (1 : Int) + d2534 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1678, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15396 pattern childGuard
    simpa only [d1678, d2534, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1678, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15414 pattern childGuard
    simpa only [d1678, d2534, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15416 (pattern : Twelve) (guard : d0 pattern = 1) : d198 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15417 (pattern : Twelve) (guard : d2496 pattern = 1) : d304 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15157 pattern childGuard
    simpa only [d2496, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15416 pattern childGuard
    simpa only [d2496, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15418 (pattern : Twelve) (guard : d0 pattern = 1) : d52 pattern ≤ (1 : Int) + d52 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15419 (pattern : Twelve) (guard : d1 pattern = 1) : d32 pattern ≤ (1 : Int) + d31 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15154 pattern childGuard
    simpa only [d32, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12187 pattern childGuard
    simpa only [d32, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15420 (pattern : Twelve) (guard : d1 pattern = 1) : d53 pattern ≤ (1 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d53, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15419 pattern childGuard
    simpa only [d53, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15421 (pattern : Twelve) (guard : d1859 pattern = 1) : d74 pattern ≤ (1 : Int) + d52 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15418 pattern childGuard
    simpa only [d1859, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15420 pattern childGuard
    simpa only [d1859, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15422 (pattern : Twelve) (guard : d0 pattern = 1) : d200 pattern ≤ (1 : Int) + d54 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15423 (pattern : Twelve) (guard : d2496 pattern = 1) : d305 pattern ≤ (1 : Int) + d2535 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d305, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15421 pattern childGuard
    simpa only [d2496, d305, d2535, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d305, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15422 pattern childGuard
    simpa only [d2496, d305, d2535, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15424 (pattern : Twelve) (guard : d2496 pattern = 1) : d320 pattern ≤ (1 : Int) + d2536 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d320, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15417 pattern childGuard
    simpa only [d320, d2536, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d320, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15423 pattern childGuard
    simpa only [d320, d2536, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15425 (pattern : Twelve) (guard : d0 pattern = 1) : d200 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15426 (pattern : Twelve) (guard : d2496 pattern = 1) : d306 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15157 pattern childGuard
    simpa only [d2496, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15425 pattern childGuard
    simpa only [d2496, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15427 (pattern : Twelve) (guard : d0 pattern = 1) : d202 pattern ≤ (1 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15428 (pattern : Twelve) (guard : d2496 pattern = 1) : d307 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15173 pattern childGuard
    simpa only [d2496, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15427 pattern childGuard
    simpa only [d2496, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15429 (pattern : Twelve) (guard : d2496 pattern = 1) : d321 pattern ≤ (1 : Int) + d2498 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d321, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15426 pattern childGuard
    simpa only [d321, d2498, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d321, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15428 pattern childGuard
    simpa only [d321, d2498, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15430 (pattern : Twelve) (guard : d2496 pattern = 1) : d332 pattern ≤ (1 : Int) + d2537 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d332, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15424 pattern childGuard
    simpa only [d332, d2537, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d332, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15429 pattern childGuard
    simpa only [d332, d2537, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15431 (pattern : Twelve) (guard : d0 pattern = 1) : d204 pattern ≤ (1 : Int) + d30 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15432 (pattern : Twelve) (guard : d2496 pattern = 1) : d308 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15181 pattern childGuard
    simpa only [d2496, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15431 pattern childGuard
    simpa only [d2496, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15433 (pattern : Twelve) (guard : d0 pattern = 1) : d206 pattern ≤ (1 : Int) + d59 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15434 (pattern : Twelve) (guard : d2496 pattern = 1) : d309 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15189 pattern childGuard
    simpa only [d2496, d309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15433 pattern childGuard
    simpa only [d2496, d309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15435 (pattern : Twelve) (guard : d2496 pattern = 1) : d322 pattern ≤ (1 : Int) + d2500 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d322, d2500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15432 pattern childGuard
    simpa only [d322, d2500, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d322, d2500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15434 pattern childGuard
    simpa only [d322, d2500, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15436 (pattern : Twelve) (guard : d0 pattern = 1) : d206 pattern ≤ (1 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15437 (pattern : Twelve) (guard : d2496 pattern = 1) : d310 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15173 pattern childGuard
    simpa only [d2496, d310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15436 pattern childGuard
    simpa only [d2496, d310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15438 (pattern : Twelve) (guard : d2496 pattern = 1) : d323 pattern ≤ (1 : Int) + d2501 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d323, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15437 pattern childGuard
    simpa only [d323, d2501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d323, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15193 pattern childGuard
    simpa only [d323, d2501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15439 (pattern : Twelve) (guard : d2496 pattern = 1) : d333 pattern ≤ (1 : Int) + d2502 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d333, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15435 pattern childGuard
    simpa only [d333, d2502, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d333, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15438 pattern childGuard
    simpa only [d333, d2502, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15440 (pattern : Twelve) (guard : d2496 pattern = 1) : d338 pattern ≤ (1 : Int) + d2538 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d338, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15430 pattern childGuard
    simpa only [d338, d2538, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d338, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15439 pattern childGuard
    simpa only [d338, d2538, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15441 (pattern : Twelve) (guard : d2496 pattern = 1) : d311 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15157 pattern childGuard
    simpa only [d2496, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11159 pattern childGuard
    simpa only [d2496, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15442 (pattern : Twelve) (guard : d1 pattern = 1) : d43 pattern ≤ (1 : Int) + d31 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15151 pattern childGuard
    simpa only [d43, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12187 pattern childGuard
    simpa only [d43, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15443 (pattern : Twelve) (guard : d1 pattern = 1) : d62 pattern ≤ (1 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d62, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15442 pattern childGuard
    simpa only [d62, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15444 (pattern : Twelve) (guard : d1859 pattern = 1) : d83 pattern ≤ (1 : Int) + d52 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15418 pattern childGuard
    simpa only [d1859, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15443 pattern childGuard
    simpa only [d1859, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15445 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d54 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15446 (pattern : Twelve) (guard : d2496 pattern = 1) : d312 pattern ≤ (1 : Int) + d2535 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d312, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15444 pattern childGuard
    simpa only [d2496, d312, d2535, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d312, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15445 pattern childGuard
    simpa only [d2496, d312, d2535, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15447 (pattern : Twelve) (guard : d2496 pattern = 1) : d324 pattern ≤ (1 : Int) + d2536 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d324, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15441 pattern childGuard
    simpa only [d324, d2536, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d324, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15446 pattern childGuard
    simpa only [d324, d2536, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15448 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (1 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15151 pattern childGuard
    simpa only [d45, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d45, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15449 (pattern : Twelve) (guard : d1 pattern = 1) : d65 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d65, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15448 pattern childGuard
    simpa only [d65, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15450 (pattern : Twelve) (guard : d1859 pattern = 1) : d85 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15170 pattern childGuard
    simpa only [d1859, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15449 pattern childGuard
    simpa only [d1859, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15451 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15452 (pattern : Twelve) (guard : d2496 pattern = 1) : d313 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15450 pattern childGuard
    simpa only [d2496, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15451 pattern childGuard
    simpa only [d2496, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15453 (pattern : Twelve) (guard : d2496 pattern = 1) : d325 pattern ≤ (1 : Int) + d2498 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d325, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15441 pattern childGuard
    simpa only [d325, d2498, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d325, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15452 pattern childGuard
    simpa only [d325, d2498, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15454 (pattern : Twelve) (guard : d2496 pattern = 1) : d334 pattern ≤ (1 : Int) + d2537 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d334, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15447 pattern childGuard
    simpa only [d334, d2537, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d334, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15453 pattern childGuard
    simpa only [d334, d2537, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15455 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15151 pattern childGuard
    simpa only [d46, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d46, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15456 (pattern : Twelve) (guard : d1 pattern = 1) : d67 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d67, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15455 pattern childGuard
    simpa only [d67, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15457 (pattern : Twelve) (guard : d1859 pattern = 1) : d87 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15178 pattern childGuard
    simpa only [d1859, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15456 pattern childGuard
    simpa only [d1859, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15458 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d30 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15459 (pattern : Twelve) (guard : d2496 pattern = 1) : d314 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15457 pattern childGuard
    simpa only [d2496, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15458 pattern childGuard
    simpa only [d2496, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15460 (pattern : Twelve) (guard : d1 pattern = 1) : d69 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12003 pattern childGuard
    simpa only [d69, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11821 pattern childGuard
    simpa only [d69, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15461 (pattern : Twelve) (guard : d1859 pattern = 1) : d89 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15184 pattern childGuard
    simpa only [d1859, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15460 pattern childGuard
    simpa only [d1859, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15462 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d59 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15463 (pattern : Twelve) (guard : d2496 pattern = 1) : d315 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15461 pattern childGuard
    simpa only [d2496, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15462 pattern childGuard
    simpa only [d2496, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15464 (pattern : Twelve) (guard : d2496 pattern = 1) : d326 pattern ≤ (1 : Int) + d2500 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d326, d2500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15459 pattern childGuard
    simpa only [d326, d2500, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d326, d2500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15463 pattern childGuard
    simpa only [d326, d2500, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15465 (pattern : Twelve) (guard : d2496 pattern = 1) : d327 pattern ≤ (1 : Int) + d2501 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d327, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15452 pattern childGuard
    simpa only [d327, d2501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d327, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15193 pattern childGuard
    simpa only [d327, d2501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15466 (pattern : Twelve) (guard : d2496 pattern = 1) : d335 pattern ≤ (1 : Int) + d2502 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d335, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15464 pattern childGuard
    simpa only [d335, d2502, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d335, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15465 pattern childGuard
    simpa only [d335, d2502, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15467 (pattern : Twelve) (guard : d2496 pattern = 1) : d339 pattern ≤ (1 : Int) + d2538 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d339, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15454 pattern childGuard
    simpa only [d339, d2538, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d339, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15466 pattern childGuard
    simpa only [d339, d2538, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15468 (pattern : Twelve) (guard : d2496 pattern = 1) : d341 pattern ≤ (1 : Int) + d2538 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15440 pattern childGuard
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15467 pattern childGuard
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15469 (pattern : Twelve) (guard : d2496 pattern = 1) : d316 pattern ≤ (1 : Int) + d2535 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d316, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15421 pattern childGuard
    simpa only [d2496, d316, d2535, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d316, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15445 pattern childGuard
    simpa only [d2496, d316, d2535, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15470 (pattern : Twelve) (guard : d2496 pattern = 1) : d328 pattern ≤ (1 : Int) + d2536 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d328, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15441 pattern childGuard
    simpa only [d328, d2536, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d328, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15469 pattern childGuard
    simpa only [d328, d2536, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15471 (pattern : Twelve) (guard : d2496 pattern = 1) : d317 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15173 pattern childGuard
    simpa only [d2496, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15451 pattern childGuard
    simpa only [d2496, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15472 (pattern : Twelve) (guard : d2496 pattern = 1) : d329 pattern ≤ (1 : Int) + d2498 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d329, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15441 pattern childGuard
    simpa only [d329, d2498, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d329, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15471 pattern childGuard
    simpa only [d329, d2498, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15473 (pattern : Twelve) (guard : d2496 pattern = 1) : d336 pattern ≤ (1 : Int) + d2537 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d336, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15470 pattern childGuard
    simpa only [d336, d2537, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d336, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15472 pattern childGuard
    simpa only [d336, d2537, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15474 (pattern : Twelve) (guard : d2496 pattern = 1) : d318 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15181 pattern childGuard
    simpa only [d2496, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15458 pattern childGuard
    simpa only [d2496, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15475 (pattern : Twelve) (guard : d2496 pattern = 1) : d319 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15189 pattern childGuard
    simpa only [d2496, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15462 pattern childGuard
    simpa only [d2496, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15476 (pattern : Twelve) (guard : d2496 pattern = 1) : d330 pattern ≤ (1 : Int) + d2500 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d330, d2500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15474 pattern childGuard
    simpa only [d330, d2500, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d330, d2500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15475 pattern childGuard
    simpa only [d330, d2500, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15477 (pattern : Twelve) (guard : d2496 pattern = 1) : d331 pattern ≤ (1 : Int) + d2501 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d331, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15471 pattern childGuard
    simpa only [d331, d2501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d331, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15193 pattern childGuard
    simpa only [d331, d2501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15478 (pattern : Twelve) (guard : d2496 pattern = 1) : d337 pattern ≤ (1 : Int) + d2502 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d337, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15476 pattern childGuard
    simpa only [d337, d2502, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d337, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15477 pattern childGuard
    simpa only [d337, d2502, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15479 (pattern : Twelve) (guard : d2496 pattern = 1) : d340 pattern ≤ (1 : Int) + d2538 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d340, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15473 pattern childGuard
    simpa only [d340, d2538, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d340, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15478 pattern childGuard
    simpa only [d340, d2538, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15480 (pattern : Twelve) (guard : d2496 pattern = 1) : d342 pattern ≤ (1 : Int) + d2538 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15479 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15467 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15481 (pattern : Twelve) (guard : d2496 pattern = 1) : d343 pattern ≤ (1 : Int) + d2538 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15468 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15480 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15482 (pattern : Twelve) (guard : d2496 pattern = 1) : d316 pattern ≤ (1 : Int) + d2539 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d316, d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15421 pattern childGuard
    simpa only [d2496, d316, d2539, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d316, d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15451 pattern childGuard
    simpa only [d2496, d316, d2539, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15483 (pattern : Twelve) (guard : d2496 pattern = 1) : d328 pattern ≤ (1 : Int) + d2540 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d328, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15441 pattern childGuard
    simpa only [d328, d2540, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d328, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15482 pattern childGuard
    simpa only [d328, d2540, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15484 (pattern : Twelve) (guard : d2496 pattern = 1) : d336 pattern ≤ (1 : Int) + d2541 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d336, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15483 pattern childGuard
    simpa only [d336, d2541, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d336, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15472 pattern childGuard
    simpa only [d336, d2541, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15485 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d132 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15486 (pattern : Twelve) (guard : d2496 pattern = 1) : d318 pattern ≤ (1 : Int) + d2542 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d318, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15181 pattern childGuard
    simpa only [d2496, d318, d2542, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d318, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15485 pattern childGuard
    simpa only [d2496, d318, d2542, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15487 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d134 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15488 (pattern : Twelve) (guard : d2496 pattern = 1) : d319 pattern ≤ (1 : Int) + d2543 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d319, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15189 pattern childGuard
    simpa only [d2496, d319, d2543, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d319, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15487 pattern childGuard
    simpa only [d2496, d319, d2543, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15489 (pattern : Twelve) (guard : d2496 pattern = 1) : d330 pattern ≤ (1 : Int) + d2544 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d330, d2544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15486 pattern childGuard
    simpa only [d330, d2544, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d330, d2544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15488 pattern childGuard
    simpa only [d330, d2544, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15490 (pattern : Twelve) (guard : d2496 pattern = 1) : d337 pattern ≤ (1 : Int) + d2545 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d337, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15489 pattern childGuard
    simpa only [d337, d2545, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d337, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15477 pattern childGuard
    simpa only [d337, d2545, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15491 (pattern : Twelve) (guard : d2496 pattern = 1) : d340 pattern ≤ (1 : Int) + d2546 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d340, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15484 pattern childGuard
    simpa only [d340, d2546, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d340, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15490 pattern childGuard
    simpa only [d340, d2546, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15492 (pattern : Twelve) (guard : d2496 pattern = 1) : d312 pattern ≤ (1 : Int) + d2539 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d312, d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15444 pattern childGuard
    simpa only [d2496, d312, d2539, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d312, d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15451 pattern childGuard
    simpa only [d2496, d312, d2539, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15493 (pattern : Twelve) (guard : d2496 pattern = 1) : d324 pattern ≤ (1 : Int) + d2540 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d324, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15441 pattern childGuard
    simpa only [d324, d2540, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d324, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15492 pattern childGuard
    simpa only [d324, d2540, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15494 (pattern : Twelve) (guard : d2496 pattern = 1) : d334 pattern ≤ (1 : Int) + d2541 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d334, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15493 pattern childGuard
    simpa only [d334, d2541, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d334, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15453 pattern childGuard
    simpa only [d334, d2541, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15495 (pattern : Twelve) (guard : d2496 pattern = 1) : d314 pattern ≤ (1 : Int) + d2542 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d314, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15457 pattern childGuard
    simpa only [d2496, d314, d2542, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d314, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15485 pattern childGuard
    simpa only [d2496, d314, d2542, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15496 (pattern : Twelve) (guard : d2496 pattern = 1) : d315 pattern ≤ (1 : Int) + d2543 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d315, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15461 pattern childGuard
    simpa only [d2496, d315, d2543, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d315, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15487 pattern childGuard
    simpa only [d2496, d315, d2543, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15497 (pattern : Twelve) (guard : d2496 pattern = 1) : d326 pattern ≤ (1 : Int) + d2544 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d326, d2544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15495 pattern childGuard
    simpa only [d326, d2544, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d326, d2544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15496 pattern childGuard
    simpa only [d326, d2544, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15498 (pattern : Twelve) (guard : d2496 pattern = 1) : d335 pattern ≤ (1 : Int) + d2545 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d335, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15497 pattern childGuard
    simpa only [d335, d2545, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d335, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15465 pattern childGuard
    simpa only [d335, d2545, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15499 (pattern : Twelve) (guard : d2496 pattern = 1) : d339 pattern ≤ (1 : Int) + d2546 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d339, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15494 pattern childGuard
    simpa only [d339, d2546, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d339, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15498 pattern childGuard
    simpa only [d339, d2546, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15500 (pattern : Twelve) (guard : d2496 pattern = 1) : d342 pattern ≤ (1 : Int) + d2546 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15491 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15499 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15501 (pattern : Twelve) (guard : d2496 pattern = 1) : d344 pattern ≤ (1 : Int) + d2547 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d344, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15481 pattern childGuard
    simpa only [d344, d2547, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d344, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15500 pattern childGuard
    simpa only [d344, d2547, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15502 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15153 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15151 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15503 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15502 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15151 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15504 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15155 pattern childGuard
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15503 pattern childGuard
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15505 (pattern : Twelve) (guard : d1859 pattern = 1) : d838 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15150 pattern childGuard
    simpa only [d1859, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15504 pattern childGuard
    simpa only [d1859, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15506 (pattern : Twelve) (guard : d0 pattern = 1) : d909 pattern ≤ (1 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15507 (pattern : Twelve) (guard : d2496 pattern = 1) : d980 pattern ≤ (1 : Int) + d2548 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d980, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15505 pattern childGuard
    simpa only [d2496, d980, d2548, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d980, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15506 pattern childGuard
    simpa only [d2496, d980, d2548, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15508 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15154 pattern childGuard
    simpa only [d34, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15186 pattern childGuard
    simpa only [d34, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15509 (pattern : Twelve) (guard : d1 pattern = 1) : d818 pattern ≤ (1 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15502 pattern childGuard
    simpa only [d818, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d818, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15510 (pattern : Twelve) (guard : d1 pattern = 1) : d826 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15508 pattern childGuard
    simpa only [d826, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15509 pattern childGuard
    simpa only [d826, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15511 (pattern : Twelve) (guard : d1859 pattern = 1) : d840 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15170 pattern childGuard
    simpa only [d1859, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15510 pattern childGuard
    simpa only [d1859, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15512 (pattern : Twelve) (guard : d0 pattern = 1) : d910 pattern ≤ (1 : Int) + d827 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15513 (pattern : Twelve) (guard : d2496 pattern = 1) : d981 pattern ≤ (1 : Int) + d2549 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d981, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15511 pattern childGuard
    simpa only [d2496, d981, d2549, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d981, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15512 pattern childGuard
    simpa only [d2496, d981, d2549, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15514 (pattern : Twelve) (guard : d2496 pattern = 1) : d991 pattern ≤ (1 : Int) + d2550 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d991, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15507 pattern childGuard
    simpa only [d991, d2550, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d991, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15513 pattern childGuard
    simpa only [d991, d2550, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15515 (pattern : Twelve) (guard : d0 pattern = 1) : d910 pattern ≤ (1 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15516 (pattern : Twelve) (guard : d2496 pattern = 1) : d982 pattern ≤ (1 : Int) + d2548 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d982, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15505 pattern childGuard
    simpa only [d2496, d982, d2548, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d982, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15515 pattern childGuard
    simpa only [d2496, d982, d2548, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15517 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d827 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15518 (pattern : Twelve) (guard : d2496 pattern = 1) : d983 pattern ≤ (1 : Int) + d2549 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d983, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15511 pattern childGuard
    simpa only [d2496, d983, d2549, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d983, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15517 pattern childGuard
    simpa only [d2496, d983, d2549, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15519 (pattern : Twelve) (guard : d2496 pattern = 1) : d992 pattern ≤ (1 : Int) + d2550 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d992, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15516 pattern childGuard
    simpa only [d992, d2550, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d992, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15518 pattern childGuard
    simpa only [d992, d2550, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15520 (pattern : Twelve) (guard : d2496 pattern = 1) : d1000 pattern ≤ (1 : Int) + d2550 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15514 pattern childGuard
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15519 pattern childGuard
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15521 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15502 pattern childGuard
    simpa only [d819, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d819, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15522 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15508 pattern childGuard
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15521 pattern childGuard
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15523 (pattern : Twelve) (guard : d1859 pattern = 1) : d842 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15178 pattern childGuard
    simpa only [d1859, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15522 pattern childGuard
    simpa only [d1859, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15524 (pattern : Twelve) (guard : d0 pattern = 1) : d911 pattern ≤ (1 : Int) + d34 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15525 (pattern : Twelve) (guard : d2496 pattern = 1) : d984 pattern ≤ (1 : Int) + d2551 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d984, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15523 pattern childGuard
    simpa only [d2496, d984, d2551, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d984, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15524 pattern childGuard
    simpa only [d2496, d984, d2551, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15526 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (1 : Int) + d4 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12142 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11195 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15527 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (1 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12142 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15526 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15528 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (1 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15186 pattern childGuard
    simpa only [d41, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15527 pattern childGuard
    simpa only [d41, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15529 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15185 pattern childGuard
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15530 (pattern : Twelve) (guard : d1 pattern = 1) : d820 pattern ≤ (1 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15529 pattern childGuard
    simpa only [d820, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d820, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15531 (pattern : Twelve) (guard : d1 pattern = 1) : d829 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15528 pattern childGuard
    simpa only [d829, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15530 pattern childGuard
    simpa only [d829, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15532 (pattern : Twelve) (guard : d1859 pattern = 1) : d844 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15184 pattern childGuard
    simpa only [d1859, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15531 pattern childGuard
    simpa only [d1859, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15533 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d830 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15534 (pattern : Twelve) (guard : d2496 pattern = 1) : d985 pattern ≤ (1 : Int) + d2552 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d985, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15532 pattern childGuard
    simpa only [d2496, d985, d2552, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d985, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15533 pattern childGuard
    simpa only [d2496, d985, d2552, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15535 (pattern : Twelve) (guard : d2496 pattern = 1) : d993 pattern ≤ (1 : Int) + d2553 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d993, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15525 pattern childGuard
    simpa only [d993, d2553, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d993, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15534 pattern childGuard
    simpa only [d993, d2553, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15536 (pattern : Twelve) (guard : d2496 pattern = 1) : d994 pattern ≤ (1 : Int) + d2554 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d994, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15518 pattern childGuard
    simpa only [d994, d2554, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d994, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15193 pattern childGuard
    simpa only [d994, d2554, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15537 (pattern : Twelve) (guard : d2496 pattern = 1) : d1001 pattern ≤ (1 : Int) + d2555 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1001, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15535 pattern childGuard
    simpa only [d1001, d2555, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1001, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15536 pattern childGuard
    simpa only [d1001, d2555, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15538 (pattern : Twelve) (guard : d2496 pattern = 1) : d1004 pattern ≤ (1 : Int) + d2556 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1004, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15520 pattern childGuard
    simpa only [d1004, d2556, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1004, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15537 pattern childGuard
    simpa only [d1004, d2556, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15539 (pattern : Twelve) (guard : d2496 pattern = 1) : d986 pattern ≤ (1 : Int) + d2548 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d986, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15505 pattern childGuard
    simpa only [d2496, d986, d2548, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d986, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11099 pattern childGuard
    simpa only [d2496, d986, d2548, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
