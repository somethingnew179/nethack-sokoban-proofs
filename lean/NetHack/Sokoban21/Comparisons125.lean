/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons124
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c17500 (pattern : Twelve) (guard : d1852 pattern = 1) : d891 pattern ≤ (1 : Int) + d883 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17498 pattern childGuard
    simpa only [d1852, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17499 pattern childGuard
    simpa only [d1852, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17501 (pattern : Twelve) (guard : d1852 pattern = 1) : d898 pattern ≤ (1 : Int) + d3193 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d898, d3193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17493 pattern childGuard
    simpa only [d898, d3193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d898, d3193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17500 pattern childGuard
    simpa only [d898, d3193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17502 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d877 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d30, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17469 pattern childGuard
    simpa only [d30, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17503 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (1 : Int) + d884 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17502 pattern childGuard
    simpa only [d56, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17449 pattern childGuard
    simpa only [d56, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17504 (pattern : Twelve) (guard : d0 pattern = 1) : d884 pattern ≤ (1 : Int) + d884 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17505 (pattern : Twelve) (guard : d1852 pattern = 1) : d892 pattern ≤ (1 : Int) + d884 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17503 pattern childGuard
    simpa only [d1852, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17504 pattern childGuard
    simpa only [d1852, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17506 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (1 : Int) + d876 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11225 pattern childGuard
    simpa only [d34, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17478 pattern childGuard
    simpa only [d34, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17507 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (1 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17506 pattern childGuard
    simpa only [d827, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17454 pattern childGuard
    simpa only [d827, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17508 (pattern : Twelve) (guard : d1852 pattern = 1) : d893 pattern ≤ (1 : Int) + d883 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17507 pattern childGuard
    simpa only [d1852, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17499 pattern childGuard
    simpa only [d1852, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17509 (pattern : Twelve) (guard : d1852 pattern = 1) : d899 pattern ≤ (1 : Int) + d3194 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d899, d3194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17505 pattern childGuard
    simpa only [d899, d3194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d899, d3194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17508 pattern childGuard
    simpa only [d899, d3194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17510 (pattern : Twelve) (guard : d1852 pattern = 1) : d902 pattern ≤ (1 : Int) + d3195 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d902, d3195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17501 pattern childGuard
    simpa only [d902, d3195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d902, d3195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17509 pattern childGuard
    simpa only [d902, d3195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17511 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11274 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17364 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17512 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11274 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17511 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17513 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d878 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17433 pattern childGuard
    simpa only [d30, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17512 pattern childGuard
    simpa only [d30, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17514 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d885 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17502 pattern childGuard
    simpa only [d885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17513 pattern childGuard
    simpa only [d885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17515 (pattern : Twelve) (guard : d0 pattern = 1) : d885 pattern ≤ (1 : Int) + d885 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17516 (pattern : Twelve) (guard : d1852 pattern = 1) : d894 pattern ≤ (1 : Int) + d885 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17514 pattern childGuard
    simpa only [d1852, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17515 pattern childGuard
    simpa only [d1852, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17517 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11233 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11231 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17518 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11233 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17517 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17519 (pattern : Twelve) (guard : d1 pattern = 1) : d879 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17440 pattern childGuard
    simpa only [d879, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17518 pattern childGuard
    simpa only [d879, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17520 (pattern : Twelve) (guard : d1 pattern = 1) : d886 pattern ≤ (1 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17506 pattern childGuard
    simpa only [d886, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17519 pattern childGuard
    simpa only [d886, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17521 (pattern : Twelve) (guard : d1852 pattern = 1) : d895 pattern ≤ (1 : Int) + d883 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17520 pattern childGuard
    simpa only [d1852, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17499 pattern childGuard
    simpa only [d1852, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17522 (pattern : Twelve) (guard : d1852 pattern = 1) : d900 pattern ≤ (1 : Int) + d3196 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d900, d3196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17516 pattern childGuard
    simpa only [d900, d3196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d900, d3196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17521 pattern childGuard
    simpa only [d900, d3196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17523 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (1 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17410 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11231 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17524 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (1 : Int) + d127 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11139 pattern childGuard
    simpa only [d38, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17523 pattern childGuard
    simpa only [d38, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17525 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d873 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17413 pattern childGuard
    simpa only [d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17511 pattern childGuard
    simpa only [d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17526 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (1 : Int) + d880 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17525 pattern childGuard
    simpa only [d39, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d39, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17527 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (1 : Int) + d887 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17524 pattern childGuard
    simpa only [d59, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17526 pattern childGuard
    simpa only [d59, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17528 (pattern : Twelve) (guard : d0 pattern = 1) : d887 pattern ≤ (1 : Int) + d887 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17529 (pattern : Twelve) (guard : d1852 pattern = 1) : d896 pattern ≤ (1 : Int) + d887 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17527 pattern childGuard
    simpa only [d1852, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17528 pattern childGuard
    simpa only [d1852, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17530 (pattern : Twelve) (guard : d1 pattern = 1) : d118 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11234 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11284 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17531 (pattern : Twelve) (guard : d1 pattern = 1) : d881 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11278 pattern childGuard
    simpa only [d881, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17530 pattern childGuard
    simpa only [d881, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17532 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17518 pattern childGuard
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17533 (pattern : Twelve) (guard : d1 pattern = 1) : d888 pattern ≤ (1 : Int) + d889 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17531 pattern childGuard
    simpa only [d888, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17532 pattern childGuard
    simpa only [d888, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17534 (pattern : Twelve) (guard : d0 pattern = 1) : d889 pattern ≤ (1 : Int) + d889 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17535 (pattern : Twelve) (guard : d1852 pattern = 1) : d897 pattern ≤ (1 : Int) + d889 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17533 pattern childGuard
    simpa only [d1852, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17534 pattern childGuard
    simpa only [d1852, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17536 (pattern : Twelve) (guard : d1852 pattern = 1) : d901 pattern ≤ (1 : Int) + d3197 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d901, d3197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17529 pattern childGuard
    simpa only [d901, d3197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d901, d3197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17535 pattern childGuard
    simpa only [d901, d3197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17537 (pattern : Twelve) (guard : d1852 pattern = 1) : d903 pattern ≤ (1 : Int) + d3198 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d903, d3198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17522 pattern childGuard
    simpa only [d903, d3198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d903, d3198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17536 pattern childGuard
    simpa only [d903, d3198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17538 (pattern : Twelve) (guard : d1852 pattern = 1) : d904 pattern ≤ (1 : Int) + d3199 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d904, d3199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17509 pattern childGuard
    simpa only [d904, d3199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d904, d3199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17373 pattern childGuard
    simpa only [d904, d3199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17539 (pattern : Twelve) (guard : d1852 pattern = 1) : d905 pattern ≤ (1 : Int) + d3200 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d905, d3200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17537 pattern childGuard
    simpa only [d905, d3200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d905, d3200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17538 pattern childGuard
    simpa only [d905, d3200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17540 (pattern : Twelve) (guard : d1852 pattern = 1) : d906 pattern ≤ (1 : Int) + d3201 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d906, d3201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17510 pattern childGuard
    simpa only [d906, d3201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d906, d3201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17539 pattern childGuard
    simpa only [d906, d3201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17541 (pattern : Twelve) (guard : d1852 pattern = 1) : d907 pattern ≤ (1 : Int) + d3202 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d907, d3202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17487 pattern childGuard
    simpa only [d907, d3202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d907, d3202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17540 pattern childGuard
    simpa only [d907, d3202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17542 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11061 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12858 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17543 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11060 pattern childGuard
    simpa only [d17, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12858 pattern childGuard
    simpa only [d17, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17544 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17542 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17543 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17545 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17544 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17543 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17546 (pattern : Twelve) (guard : d0 pattern = 1) : d1284 pattern ≤ (1 : Int) + d1284 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17547 (pattern : Twelve) (guard : d1852 pattern = 1) : d1293 pattern ≤ (1 : Int) + d1284 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17545 pattern childGuard
    simpa only [d1852, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17546 pattern childGuard
    simpa only [d1852, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17548 (pattern : Twelve) (guard : d1852 pattern = 1) : d1294 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11407 pattern childGuard
    simpa only [d1852, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1852, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17549 (pattern : Twelve) (guard : d1852 pattern = 1) : d1305 pattern ≤ (1 : Int) + d3203 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1305, d3203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17547 pattern childGuard
    simpa only [d1305, d3203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1305, d3203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17548 pattern childGuard
    simpa only [d1305, d3203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17550 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (1 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11138 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12865 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17551 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (1 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17542 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17550 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17552 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (1 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17543 pattern childGuard
    simpa only [d36, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d36, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17553 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (1 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17551 pattern childGuard
    simpa only [d827, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17552 pattern childGuard
    simpa only [d827, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17554 (pattern : Twelve) (guard : d0 pattern = 1) : d1285 pattern ≤ (1 : Int) + d1285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17555 (pattern : Twelve) (guard : d1852 pattern = 1) : d1295 pattern ≤ (1 : Int) + d1285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17553 pattern childGuard
    simpa only [d1852, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17554 pattern childGuard
    simpa only [d1852, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17556 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11407 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11236 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17557 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11407 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17558 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17556 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17557 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17559 (pattern : Twelve) (guard : d1852 pattern = 1) : d1296 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17558 pattern childGuard
    simpa only [d1852, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1852, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17560 (pattern : Twelve) (guard : d1852 pattern = 1) : d1306 pattern ≤ (1 : Int) + d3204 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1306, d3204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17555 pattern childGuard
    simpa only [d1306, d3204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1306, d3204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17559 pattern childGuard
    simpa only [d1306, d3204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17561 (pattern : Twelve) (guard : d1852 pattern = 1) : d1313 pattern ≤ (1 : Int) + d3205 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1313, d3205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17549 pattern childGuard
    simpa only [d1313, d3205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1313, d3205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17560 pattern childGuard
    simpa only [d1313, d3205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17562 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (1 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d23, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12865 pattern childGuard
    simpa only [d23, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17563 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (1 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17543 pattern childGuard
    simpa only [d34, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17562 pattern childGuard
    simpa only [d34, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17564 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (1 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17551 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17563 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17565 (pattern : Twelve) (guard : d0 pattern = 1) : d1287 pattern ≤ (1 : Int) + d1287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17566 (pattern : Twelve) (guard : d1852 pattern = 1) : d1297 pattern ≤ (1 : Int) + d1287 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17564 pattern childGuard
    simpa only [d1852, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17565 pattern childGuard
    simpa only [d1852, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17567 (pattern : Twelve) (guard : d1852 pattern = 1) : d1298 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17556 pattern childGuard
    simpa only [d1852, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1852, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17568 (pattern : Twelve) (guard : d1852 pattern = 1) : d1307 pattern ≤ (1 : Int) + d3206 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1307, d3206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17566 pattern childGuard
    simpa only [d1307, d3206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1307, d3206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17567 pattern childGuard
    simpa only [d1307, d3206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17569 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (1 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12489 pattern childGuard
    simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12584 pattern childGuard
    simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17570 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (1 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17550 pattern childGuard
    simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17569 pattern childGuard
    simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17571 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (1 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17562 pattern childGuard
    simpa only [d40, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d40, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17572 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (1 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17570 pattern childGuard
    simpa only [d830, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17571 pattern childGuard
    simpa only [d830, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17573 (pattern : Twelve) (guard : d0 pattern = 1) : d1288 pattern ≤ (1 : Int) + d1288 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17574 (pattern : Twelve) (guard : d1852 pattern = 1) : d1299 pattern ≤ (1 : Int) + d1288 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17572 pattern childGuard
    simpa only [d1852, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17573 pattern childGuard
    simpa only [d1852, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17575 (pattern : Twelve) (guard : d1852 pattern = 1) : d1308 pattern ≤ (1 : Int) + d3207 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1308, d3207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17574 pattern childGuard
    simpa only [d1308, d3207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1308, d3207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11949 pattern childGuard
    simpa only [d1308, d3207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17576 (pattern : Twelve) (guard : d1852 pattern = 1) : d1314 pattern ≤ (1 : Int) + d3208 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1314, d3208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17568 pattern childGuard
    simpa only [d1314, d3208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1314, d3208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17575 pattern childGuard
    simpa only [d1314, d3208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17577 (pattern : Twelve) (guard : d1852 pattern = 1) : d1315 pattern ≤ (1 : Int) + d3209 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1315, d3209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17560 pattern childGuard
    simpa only [d1315, d3209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1315, d3209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17373 pattern childGuard
    simpa only [d1315, d3209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17578 (pattern : Twelve) (guard : d1852 pattern = 1) : d1319 pattern ≤ (1 : Int) + d3210 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1319, d3210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17576 pattern childGuard
    simpa only [d1319, d3210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1319, d3210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17577 pattern childGuard
    simpa only [d1319, d3210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17579 (pattern : Twelve) (guard : d1852 pattern = 1) : d1321 pattern ≤ (1 : Int) + d3211 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1321, d3211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17561 pattern childGuard
    simpa only [d1321, d3211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1321, d3211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17578 pattern childGuard
    simpa only [d1321, d3211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17580 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (1 : Int) + d4 pattern := by
  change (1 : Int) ≤ (1 : Int) + 4
  decide
theorem c17581 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (1 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11221 pattern childGuard
    simpa only [d7, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17580 pattern childGuard
    simpa only [d7, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17582 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17323 pattern childGuard
    simpa only [d17, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17581 pattern childGuard
    simpa only [d17, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17583 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17542 pattern childGuard
    simpa only [d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17582 pattern childGuard
    simpa only [d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17584 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17543 pattern childGuard
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17582 pattern childGuard
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17585 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17583 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17584 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17586 (pattern : Twelve) (guard : d0 pattern = 1) : d1333 pattern ≤ (1 : Int) + d1333 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17587 (pattern : Twelve) (guard : d1852 pattern = 1) : d1339 pattern ≤ (1 : Int) + d1333 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17585 pattern childGuard
    simpa only [d1852, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17586 pattern childGuard
    simpa only [d1852, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17588 (pattern : Twelve) (guard : d1852 pattern = 1) : d1345 pattern ≤ (1 : Int) + d3212 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1345, d3212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17587 pattern childGuard
    simpa only [d1345, d3212, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1345, d3212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17548 pattern childGuard
    simpa only [d1345, d3212, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17589 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (1 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17542 pattern childGuard
    simpa only [d34, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17562 pattern childGuard
    simpa only [d34, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17590 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (1 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17589 pattern childGuard
    simpa only [d827, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17552 pattern childGuard
    simpa only [d827, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17591 (pattern : Twelve) (guard : d0 pattern = 1) : d1334 pattern ≤ (1 : Int) + d1334 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17592 (pattern : Twelve) (guard : d1852 pattern = 1) : d1340 pattern ≤ (1 : Int) + d1334 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17590 pattern childGuard
    simpa only [d1852, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17591 pattern childGuard
    simpa only [d1852, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17593 (pattern : Twelve) (guard : d1852 pattern = 1) : d1346 pattern ≤ (1 : Int) + d3213 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1346, d3213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17592 pattern childGuard
    simpa only [d1346, d3213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1346, d3213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17559 pattern childGuard
    simpa only [d1346, d3213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17594 (pattern : Twelve) (guard : d1852 pattern = 1) : d1349 pattern ≤ (1 : Int) + d3214 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1349, d3214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17588 pattern childGuard
    simpa only [d1349, d3214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1349, d3214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17593 pattern childGuard
    simpa only [d1349, d3214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17595 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (1 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17511 pattern childGuard
    simpa only [d23, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17477 pattern childGuard
    simpa only [d23, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17596 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (1 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17543 pattern childGuard
    simpa only [d34, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17595 pattern childGuard
    simpa only [d34, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17597 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (1 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17589 pattern childGuard
    simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17596 pattern childGuard
    simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17598 (pattern : Twelve) (guard : d0 pattern = 1) : d1335 pattern ≤ (1 : Int) + d1335 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17599 (pattern : Twelve) (guard : d1852 pattern = 1) : d1341 pattern ≤ (1 : Int) + d1335 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17597 pattern childGuard
    simpa only [d1852, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17598 pattern childGuard
    simpa only [d1852, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17600 (pattern : Twelve) (guard : d1 pattern = 1) : d1329 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11407 pattern childGuard
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11419 pattern childGuard
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17601 (pattern : Twelve) (guard : d1 pattern = 1) : d1336 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17556 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17600 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17602 (pattern : Twelve) (guard : d1852 pattern = 1) : d1342 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17601 pattern childGuard
    simpa only [d1852, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1852, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17603 (pattern : Twelve) (guard : d1852 pattern = 1) : d1347 pattern ≤ (1 : Int) + d3215 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1347, d3215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17599 pattern childGuard
    simpa only [d1347, d3215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1347, d3215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17602 pattern childGuard
    simpa only [d1347, d3215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17604 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11231 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11234 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17605 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11231 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17604 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17606 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (1 : Int) + d1330 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17550 pattern childGuard
    simpa only [d41, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17605 pattern childGuard
    simpa only [d41, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17607 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (1 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17595 pattern childGuard
    simpa only [d40, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d40, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17608 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (1 : Int) + d1337 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17606 pattern childGuard
    simpa only [d830, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17607 pattern childGuard
    simpa only [d830, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17609 (pattern : Twelve) (guard : d0 pattern = 1) : d1337 pattern ≤ (1 : Int) + d1337 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17610 (pattern : Twelve) (guard : d1852 pattern = 1) : d1343 pattern ≤ (1 : Int) + d1337 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17608 pattern childGuard
    simpa only [d1852, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17609 pattern childGuard
    simpa only [d1852, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17611 (pattern : Twelve) (guard : d1 pattern = 1) : d1332 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11236 pattern childGuard
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11431 pattern childGuard
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17612 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11419 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17613 (pattern : Twelve) (guard : d1 pattern = 1) : d1338 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17611 pattern childGuard
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17612 pattern childGuard
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17614 (pattern : Twelve) (guard : d1852 pattern = 1) : d1344 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17613 pattern childGuard
    simpa only [d1852, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1852, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17615 (pattern : Twelve) (guard : d1852 pattern = 1) : d1348 pattern ≤ (1 : Int) + d3216 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1348, d3216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17610 pattern childGuard
    simpa only [d1348, d3216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1348, d3216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17614 pattern childGuard
    simpa only [d1348, d3216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17616 (pattern : Twelve) (guard : d1852 pattern = 1) : d1350 pattern ≤ (1 : Int) + d3217 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1350, d3217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17603 pattern childGuard
    simpa only [d1350, d3217, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1350, d3217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17615 pattern childGuard
    simpa only [d1350, d3217, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17617 (pattern : Twelve) (guard : d1852 pattern = 1) : d1351 pattern ≤ (1 : Int) + d3218 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1351, d3218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17593 pattern childGuard
    simpa only [d1351, d3218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1351, d3218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17373 pattern childGuard
    simpa only [d1351, d3218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17618 (pattern : Twelve) (guard : d1852 pattern = 1) : d1352 pattern ≤ (1 : Int) + d3219 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1352, d3219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17616 pattern childGuard
    simpa only [d1352, d3219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1352, d3219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17617 pattern childGuard
    simpa only [d1352, d3219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17619 (pattern : Twelve) (guard : d1852 pattern = 1) : d1353 pattern ≤ (1 : Int) + d3220 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1353, d3220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17594 pattern childGuard
    simpa only [d1353, d3220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1353, d3220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17618 pattern childGuard
    simpa only [d1353, d3220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17620 (pattern : Twelve) (guard : d1852 pattern = 1) : d1354 pattern ≤ (1 : Int) + d3221 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1354, d3221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17579 pattern childGuard
    simpa only [d1354, d3221, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1354, d3221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17619 pattern childGuard
    simpa only [d1354, d3221, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17621 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12685 pattern childGuard
    simpa only [d19, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12891 pattern childGuard
    simpa only [d19, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17622 (pattern : Twelve) (guard : d0 pattern = 1) : d1324 pattern ≤ (1 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17623 (pattern : Twelve) (guard : d1852 pattern = 1) : d1649 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17621 pattern childGuard
    simpa only [d1852, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17622 pattern childGuard
    simpa only [d1852, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17624 (pattern : Twelve) (guard : d1852 pattern = 1) : d1656 pattern ≤ (1 : Int) + d2404 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1656, d2404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17623 pattern childGuard
    simpa only [d1656, d2404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1656, d2404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11943 pattern childGuard
    simpa only [d1656, d2404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17625 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (1 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12734 pattern childGuard
    simpa only [d25, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11392 pattern childGuard
    simpa only [d25, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17626 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17621 pattern childGuard
    simpa only [d817, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17625 pattern childGuard
    simpa only [d817, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17627 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (1 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17621 pattern childGuard
    simpa only [d29, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d29, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17628 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (1 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17626 pattern childGuard
    simpa only [d1286, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17627 pattern childGuard
    simpa only [d1286, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17629 (pattern : Twelve) (guard : d0 pattern = 1) : d1647 pattern ≤ (1 : Int) + d1647 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17630 (pattern : Twelve) (guard : d1852 pattern = 1) : d1651 pattern ≤ (1 : Int) + d1647 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17628 pattern childGuard
    simpa only [d1852, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17629 pattern childGuard
    simpa only [d1852, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17631 (pattern : Twelve) (guard : d1852 pattern = 1) : d1657 pattern ≤ (1 : Int) + d3222 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1657, d3222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17630 pattern childGuard
    simpa only [d1657, d3222, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1657, d3222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11949 pattern childGuard
    simpa only [d1657, d3222, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17632 (pattern : Twelve) (guard : d1852 pattern = 1) : d1660 pattern ≤ (1 : Int) + d3223 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1660, d3223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17624 pattern childGuard
    simpa only [d1660, d3223, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1660, d3223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17631 pattern childGuard
    simpa only [d1660, d3223, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17633 (pattern : Twelve) (guard : d0 pattern = 1) : d1644 pattern ≤ (1 : Int) + d1644 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17634 (pattern : Twelve) (guard : d1852 pattern = 1) : d1652 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17626 pattern childGuard
    simpa only [d1852, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17633 pattern childGuard
    simpa only [d1852, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17635 (pattern : Twelve) (guard : d1852 pattern = 1) : d1658 pattern ≤ (1 : Int) + d3224 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1658, d3224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17634 pattern childGuard
    simpa only [d1658, d3224, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1658, d3224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11953 pattern childGuard
    simpa only [d1658, d3224, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17636 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (1 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17625 pattern childGuard
    simpa only [d821, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15161 pattern childGuard
    simpa only [d821, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17637 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (1 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17625 pattern childGuard
    simpa only [d42, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d42, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17638 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (1 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17636 pattern childGuard
    simpa only [d1289, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17637 pattern childGuard
    simpa only [d1289, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17639 (pattern : Twelve) (guard : d0 pattern = 1) : d1648 pattern ≤ (1 : Int) + d1648 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban21.Diagram
