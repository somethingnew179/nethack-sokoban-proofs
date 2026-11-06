/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons031
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c4480 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4481 (pattern : Twelve) (guard : d1848 pattern = 1) : d27 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d27, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d27, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d27, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4480 pattern childGuard
    simpa only [d1848, d27, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4482 (pattern : Twelve) (guard : d1849 pattern = 1) : d824 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d824, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4481 pattern childGuard
    simpa only [d1849, d824, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d824, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c256 pattern childGuard
    simpa only [d1849, d824, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4483 (pattern : Twelve) (guard : d1849 pattern = 1) : d838 pattern ≤ (0 : Int) + d265 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d838, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4412 pattern childGuard
    simpa only [d838, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d838, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4482 pattern childGuard
    simpa only [d838, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4484 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (0 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4485 (pattern : Twelve) (guard : d1848 pattern = 1) : d17 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4484 pattern childGuard
    simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4486 (pattern : Twelve) (guard : d1849 pattern = 1) : d17 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4485 pattern childGuard
    simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c259 pattern childGuard
    simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4487 (pattern : Twelve) (guard : d1849 pattern = 1) : d839 pattern ≤ (0 : Int) + d949 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d839, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4486 pattern childGuard
    simpa only [d839, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d839, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4467 pattern childGuard
    simpa only [d839, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4488 (pattern : Twelve) (guard : d1849 pattern = 1) : d853 pattern ≤ (0 : Int) + d959 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d853, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d853, d959, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d853, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4487 pattern childGuard
    simpa only [d853, d959, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4489 (pattern : Twelve) (guard : d0 pattern = 1) : d916 pattern ≤ (0 : Int) + d960 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4490 (pattern : Twelve) (guard : d1857 pattern = 1) : d1020 pattern ≤ (0 : Int) + d965 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1020, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4488 pattern childGuard
    simpa only [d1857, d1020, d965, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1020, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4489 pattern childGuard
    simpa only [d1857, d1020, d965, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4491 (pattern : Twelve) (guard : d1849 pattern = 1) : d838 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d838, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4424 pattern childGuard
    simpa only [d838, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d838, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4482 pattern childGuard
    simpa only [d838, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4492 (pattern : Twelve) (guard : d1849 pattern = 1) : d853 pattern ≤ (0 : Int) + d958 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d853, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4491 pattern childGuard
    simpa only [d853, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d853, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4487 pattern childGuard
    simpa only [d853, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4493 (pattern : Twelve) (guard : d1857 pattern = 1) : d1021 pattern ≤ (0 : Int) + d966 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1021, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4492 pattern childGuard
    simpa only [d1857, d1021, d966, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1021, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1857, d1021, d966, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4494 (pattern : Twelve) (guard : d1857 pattern = 1) : d1024 pattern ≤ (0 : Int) + d971 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1024, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4490 pattern childGuard
    simpa only [d1024, d971, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1024, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4493 pattern childGuard
    simpa only [d1024, d971, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4495 (pattern : Twelve) (guard : d1857 pattern = 1) : d1025 pattern ≤ (0 : Int) + d973 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1025, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4479 pattern childGuard
    simpa only [d1025, d973, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1025, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4494 pattern childGuard
    simpa only [d1025, d973, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4496 (pattern : Twelve) (guard : d1849 pattern = 1) : d838 pattern ≤ (0 : Int) + d953 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d838, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4430 pattern childGuard
    simpa only [d838, d953, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d838, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4472 pattern childGuard
    simpa only [d838, d953, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4497 (pattern : Twelve) (guard : d1849 pattern = 1) : d823 pattern ≤ (0 : Int) + d946 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1934 pattern childGuard
    simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c289 pattern childGuard
    simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4498 (pattern : Twelve) (guard : d1849 pattern = 1) : d846 pattern ≤ (0 : Int) + d954 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d846, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4497 pattern childGuard
    simpa only [d846, d954, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d846, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4467 pattern childGuard
    simpa only [d846, d954, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4499 (pattern : Twelve) (guard : d1849 pattern = 1) : d857 pattern ≤ (0 : Int) + d961 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d857, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4496 pattern childGuard
    simpa only [d857, d961, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d857, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4498 pattern childGuard
    simpa only [d857, d961, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4500 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d958 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4501 (pattern : Twelve) (guard : d1857 pattern = 1) : d1022 pattern ≤ (0 : Int) + d967 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1022, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4499 pattern childGuard
    simpa only [d1857, d1022, d967, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1022, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4500 pattern childGuard
    simpa only [d1857, d1022, d967, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4502 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4503 (pattern : Twelve) (guard : d1848 pattern = 1) : d823 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d823, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d823, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d823, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4502 pattern childGuard
    simpa only [d1848, d823, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4504 (pattern : Twelve) (guard : d1849 pattern = 1) : d823 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4503 pattern childGuard
    simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c289 pattern childGuard
    simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4505 (pattern : Twelve) (guard : d1849 pattern = 1) : d846 pattern ≤ (0 : Int) + d949 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d846, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4504 pattern childGuard
    simpa only [d846, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d846, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4467 pattern childGuard
    simpa only [d846, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4506 (pattern : Twelve) (guard : d1849 pattern = 1) : d857 pattern ≤ (0 : Int) + d958 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d857, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4491 pattern childGuard
    simpa only [d857, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d857, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4505 pattern childGuard
    simpa only [d857, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4507 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d960 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4508 (pattern : Twelve) (guard : d1857 pattern = 1) : d1022 pattern ≤ (0 : Int) + d968 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1022, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4506 pattern childGuard
    simpa only [d1857, d1022, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1022, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4507 pattern childGuard
    simpa only [d1857, d1022, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4509 (pattern : Twelve) (guard : d1857 pattern = 1) : d1022 pattern ≤ (0 : Int) + d966 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1022, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4506 pattern childGuard
    simpa only [d1857, d1022, d966, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1022, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1857, d1022, d966, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4510 (pattern : Twelve) (guard : d1857 pattern = 1) : d1022 pattern ≤ (0 : Int) + d972 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4508 pattern childGuard
    simpa only [d972, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4509 pattern childGuard
    simpa only [d972, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4511 (pattern : Twelve) (guard : d1857 pattern = 1) : d1022 pattern ≤ (0 : Int) + d974 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4501 pattern childGuard
    simpa only [d974, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4510 pattern childGuard
    simpa only [d974, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4512 (pattern : Twelve) (guard : d1857 pattern = 1) : d1026 pattern ≤ (0 : Int) + d976 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1026, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4495 pattern childGuard
    simpa only [d1026, d976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1026, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4511 pattern childGuard
    simpa only [d1026, d976, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4513 (pattern : Twelve) (guard : d1849 pattern = 1) : d853 pattern ≤ (0 : Int) + d962 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d853, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4496 pattern childGuard
    simpa only [d853, d962, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d853, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4475 pattern childGuard
    simpa only [d853, d962, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4514 (pattern : Twelve) (guard : d1857 pattern = 1) : d1021 pattern ≤ (0 : Int) + d969 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1021, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4513 pattern childGuard
    simpa only [d1857, d1021, d969, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1021, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4500 pattern childGuard
    simpa only [d1857, d1021, d969, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4515 (pattern : Twelve) (guard : d1857 pattern = 1) : d1021 pattern ≤ (0 : Int) + d968 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1021, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4492 pattern childGuard
    simpa only [d1857, d1021, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1021, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4507 pattern childGuard
    simpa only [d1857, d1021, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4516 (pattern : Twelve) (guard : d1857 pattern = 1) : d1021 pattern ≤ (0 : Int) + d972 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4515 pattern childGuard
    simpa only [d972, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4493 pattern childGuard
    simpa only [d972, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4517 (pattern : Twelve) (guard : d1857 pattern = 1) : d1021 pattern ≤ (0 : Int) + d975 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4514 pattern childGuard
    simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4516 pattern childGuard
    simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4518 (pattern : Twelve) (guard : d1857 pattern = 1) : d1027 pattern ≤ (0 : Int) + d977 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1027, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4517 pattern childGuard
    simpa only [d1027, d977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1027, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4511 pattern childGuard
    simpa only [d1027, d977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4519 (pattern : Twelve) (guard : d1857 pattern = 1) : d1028 pattern ≤ (0 : Int) + d978 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1028, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4512 pattern childGuard
    simpa only [d1028, d978, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1028, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4518 pattern childGuard
    simpa only [d1028, d978, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4520 (pattern : Twelve) (guard : d1857 pattern = 1) : d1029 pattern ≤ (0 : Int) + d979 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1029, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4519 pattern childGuard
    simpa only [d1029, d979, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1029, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4518 pattern childGuard
    simpa only [d1029, d979, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4521 (pattern : Twelve) (guard : d1849 pattern = 1) : d1284 pattern ≤ (0 : Int) + d1380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1284, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1959 pattern childGuard
    simpa only [d1849, d1284, d1380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1284, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c325 pattern childGuard
    simpa only [d1849, d1284, d1380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4522 (pattern : Twelve) (guard : d1849 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1385 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1293, d1385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4466 pattern childGuard
    simpa only [d1293, d1385, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1293, d1385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4521 pattern childGuard
    simpa only [d1293, d1385, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4523 (pattern : Twelve) (guard : d1849 pattern = 1) : d19 pattern ≤ (0 : Int) + d1381 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1741 pattern childGuard
    simpa only [d1849, d1381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c329 pattern childGuard
    simpa only [d1849, d1381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4524 (pattern : Twelve) (guard : d1849 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1386 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1294, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4523 pattern childGuard
    simpa only [d1294, d1386, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1294, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1294, d1386, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4525 (pattern : Twelve) (guard : d1849 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1393 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1305, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4522 pattern childGuard
    simpa only [d1305, d1393, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1305, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4524 pattern childGuard
    simpa only [d1305, d1393, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4526 (pattern : Twelve) (guard : d0 pattern = 1) : d1357 pattern ≤ (0 : Int) + d1394 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4527 (pattern : Twelve) (guard : d1857 pattern = 1) : d1435 pattern ≤ (0 : Int) + d1398 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1435, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4525 pattern childGuard
    simpa only [d1857, d1435, d1398, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1435, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4526 pattern childGuard
    simpa only [d1857, d1435, d1398, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4528 (pattern : Twelve) (guard : d1849 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1389 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1293, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4474 pattern childGuard
    simpa only [d1293, d1389, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1293, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4521 pattern childGuard
    simpa only [d1293, d1389, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4529 (pattern : Twelve) (guard : d1849 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1395 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1305, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4528 pattern childGuard
    simpa only [d1305, d1395, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1305, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4524 pattern childGuard
    simpa only [d1305, d1395, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4530 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1394 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4531 (pattern : Twelve) (guard : d1857 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1399 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1436, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4529 pattern childGuard
    simpa only [d1857, d1436, d1399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1436, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4530 pattern childGuard
    simpa only [d1857, d1436, d1399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4532 (pattern : Twelve) (guard : d1857 pattern = 1) : d1438 pattern ≤ (0 : Int) + d1403 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1438, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4527 pattern childGuard
    simpa only [d1438, d1403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1438, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4531 pattern childGuard
    simpa only [d1438, d1403, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4533 (pattern : Twelve) (guard : d0 pattern = 1) : d872 pattern ≤ (0 : Int) + d1276 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4534 (pattern : Twelve) (guard : d1848 pattern = 1) : d1278 pattern ≤ (0 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1278, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1469 pattern childGuard
    simpa only [d1848, d1278, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1278, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4533 pattern childGuard
    simpa only [d1848, d1278, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4535 (pattern : Twelve) (guard : d1849 pattern = 1) : d1284 pattern ≤ (0 : Int) + d1382 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1284, d1382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4534 pattern childGuard
    simpa only [d1849, d1284, d1382, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1284, d1382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c325 pattern childGuard
    simpa only [d1849, d1284, d1382, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4536 (pattern : Twelve) (guard : d1849 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1387 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1293, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4486 pattern childGuard
    simpa only [d1293, d1387, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1293, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4535 pattern childGuard
    simpa only [d1293, d1387, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4537 (pattern : Twelve) (guard : d0 pattern = 1) : d19 pattern ≤ (0 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4538 (pattern : Twelve) (guard : d1848 pattern = 1) : d19 pattern ≤ (0 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4537 pattern childGuard
    simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4539 (pattern : Twelve) (guard : d1849 pattern = 1) : d19 pattern ≤ (0 : Int) + d942 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4538 pattern childGuard
    simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c329 pattern childGuard
    simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4540 (pattern : Twelve) (guard : d1849 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1388 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1294, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4539 pattern childGuard
    simpa only [d1294, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1294, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1294, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4541 (pattern : Twelve) (guard : d1849 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1394 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1305, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4536 pattern childGuard
    simpa only [d1305, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1305, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4540 pattern childGuard
    simpa only [d1305, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4542 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1396 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4543 (pattern : Twelve) (guard : d1857 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1400 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1436, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4541 pattern childGuard
    simpa only [d1857, d1436, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1436, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4542 pattern childGuard
    simpa only [d1857, d1436, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4544 (pattern : Twelve) (guard : d1857 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1401 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1436, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4541 pattern childGuard
    simpa only [d1857, d1436, d1401, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1436, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1857, d1436, d1401, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4545 (pattern : Twelve) (guard : d1857 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1404 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4543 pattern childGuard
    simpa only [d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4544 pattern childGuard
    simpa only [d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4546 (pattern : Twelve) (guard : d1857 pattern = 1) : d1439 pattern ≤ (0 : Int) + d1405 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1439, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4532 pattern childGuard
    simpa only [d1439, d1405, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1439, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4545 pattern childGuard
    simpa only [d1439, d1405, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4547 (pattern : Twelve) (guard : d1849 pattern = 1) : d1283 pattern ≤ (0 : Int) + d1384 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1985 pattern childGuard
    simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c364 pattern childGuard
    simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4548 (pattern : Twelve) (guard : d1849 pattern = 1) : d1301 pattern ≤ (0 : Int) + d1392 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1301, d1392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4547 pattern childGuard
    simpa only [d1301, d1392, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1301, d1392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1301, d1392, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4549 (pattern : Twelve) (guard : d1849 pattern = 1) : d1309 pattern ≤ (0 : Int) + d1397 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1309, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4528 pattern childGuard
    simpa only [d1309, d1397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1309, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4548 pattern childGuard
    simpa only [d1309, d1397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4550 (pattern : Twelve) (guard : d1857 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1402 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1437, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4549 pattern childGuard
    simpa only [d1857, d1437, d1402, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1437, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4530 pattern childGuard
    simpa only [d1857, d1437, d1402, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4551 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (0 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4552 (pattern : Twelve) (guard : d1848 pattern = 1) : d1283 pattern ≤ (0 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1283, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d1283, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1283, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4551 pattern childGuard
    simpa only [d1848, d1283, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4553 (pattern : Twelve) (guard : d1849 pattern = 1) : d1283 pattern ≤ (0 : Int) + d942 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4552 pattern childGuard
    simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c364 pattern childGuard
    simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4554 (pattern : Twelve) (guard : d1849 pattern = 1) : d1301 pattern ≤ (0 : Int) + d1388 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1301, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4553 pattern childGuard
    simpa only [d1301, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1301, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1301, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4555 (pattern : Twelve) (guard : d1849 pattern = 1) : d1309 pattern ≤ (0 : Int) + d1394 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1309, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4536 pattern childGuard
    simpa only [d1309, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1309, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4554 pattern childGuard
    simpa only [d1309, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4556 (pattern : Twelve) (guard : d1857 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1400 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1437, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4555 pattern childGuard
    simpa only [d1857, d1437, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1437, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4542 pattern childGuard
    simpa only [d1857, d1437, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4557 (pattern : Twelve) (guard : d1857 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1401 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1437, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4555 pattern childGuard
    simpa only [d1857, d1437, d1401, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1437, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1857, d1437, d1401, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4558 (pattern : Twelve) (guard : d1857 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1404 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4556 pattern childGuard
    simpa only [d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4557 pattern childGuard
    simpa only [d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4559 (pattern : Twelve) (guard : d1857 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1406 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4550 pattern childGuard
    simpa only [d1406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4558 pattern childGuard
    simpa only [d1406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4560 (pattern : Twelve) (guard : d1857 pattern = 1) : d1440 pattern ≤ (0 : Int) + d1408 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1440, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4546 pattern childGuard
    simpa only [d1440, d1408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1440, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4559 pattern childGuard
    simpa only [d1440, d1408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4561 (pattern : Twelve) (guard : d1857 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1407 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4531 pattern childGuard
    simpa only [d1407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4545 pattern childGuard
    simpa only [d1407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4562 (pattern : Twelve) (guard : d1857 pattern = 1) : d1441 pattern ≤ (0 : Int) + d1409 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1441, d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4561 pattern childGuard
    simpa only [d1441, d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1441, d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4559 pattern childGuard
    simpa only [d1441, d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4563 (pattern : Twelve) (guard : d1857 pattern = 1) : d1442 pattern ≤ (0 : Int) + d1410 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1442, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4560 pattern childGuard
    simpa only [d1442, d1410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1442, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4562 pattern childGuard
    simpa only [d1442, d1410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4564 (pattern : Twelve) (guard : d1857 pattern = 1) : d1443 pattern ≤ (0 : Int) + d1411 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1443, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4563 pattern childGuard
    simpa only [d1443, d1411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1443, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4562 pattern childGuard
    simpa only [d1443, d1411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4565 (pattern : Twelve) (guard : d1849 pattern = 1) : d1324 pattern ≤ (0 : Int) + d1689 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2004 pattern childGuard
    simpa only [d1849, d1689, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c389 pattern childGuard
    simpa only [d1849, d1689, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4566 (pattern : Twelve) (guard : d1849 pattern = 1) : d1649 pattern ≤ (0 : Int) + d1693 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1649, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4523 pattern childGuard
    simpa only [d1649, d1693, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1649, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4565 pattern childGuard
    simpa only [d1649, d1693, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4567 (pattern : Twelve) (guard : d1849 pattern = 1) : d25 pattern ≤ (0 : Int) + d1690 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1799 pattern childGuard
    simpa only [d1849, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d1849, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4568 (pattern : Twelve) (guard : d1849 pattern = 1) : d1650 pattern ≤ (0 : Int) + d1694 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1650, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4567 pattern childGuard
    simpa only [d1650, d1694, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1650, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1650, d1694, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4569 (pattern : Twelve) (guard : d1849 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1697 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1656, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4566 pattern childGuard
    simpa only [d1656, d1697, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1656, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4568 pattern childGuard
    simpa only [d1656, d1697, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4570 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1698 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4571 (pattern : Twelve) (guard : d1857 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1700 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1715, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4569 pattern childGuard
    simpa only [d1857, d1715, d1700, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1715, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4570 pattern childGuard
    simpa only [d1857, d1715, d1700, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4572 (pattern : Twelve) (guard : d0 pattern = 1) : d1324 pattern ≤ (0 : Int) + d20 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4573 (pattern : Twelve) (guard : d1848 pattern = 1) : d1324 pattern ≤ (0 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c388 pattern childGuard
    simpa only [d1848, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4572 pattern childGuard
    simpa only [d1848, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4574 (pattern : Twelve) (guard : d1849 pattern = 1) : d1324 pattern ≤ (0 : Int) + d1691 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4573 pattern childGuard
    simpa only [d1849, d1691, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c389 pattern childGuard
    simpa only [d1849, d1691, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4575 (pattern : Twelve) (guard : d1849 pattern = 1) : d1649 pattern ≤ (0 : Int) + d1695 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1649, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4539 pattern childGuard
    simpa only [d1649, d1695, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1649, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4574 pattern childGuard
    simpa only [d1649, d1695, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4576 (pattern : Twelve) (guard : d0 pattern = 1) : d25 pattern ≤ (0 : Int) + d21 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4577 (pattern : Twelve) (guard : d1848 pattern = 1) : d25 pattern ≤ (0 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c392 pattern childGuard
    simpa only [d1848, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4576 pattern childGuard
    simpa only [d1848, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4578 (pattern : Twelve) (guard : d1849 pattern = 1) : d25 pattern ≤ (0 : Int) + d945 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4577 pattern childGuard
    simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4579 (pattern : Twelve) (guard : d1849 pattern = 1) : d1650 pattern ≤ (0 : Int) + d1391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1650, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4578 pattern childGuard
    simpa only [d1650, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1650, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1650, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4580 (pattern : Twelve) (guard : d1849 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1698 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1656, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4575 pattern childGuard
    simpa only [d1656, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1656, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4579 pattern childGuard
    simpa only [d1656, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4581 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1699 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4582 (pattern : Twelve) (guard : d1857 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1701 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1715, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4580 pattern childGuard
    simpa only [d1857, d1715, d1701, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1715, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4581 pattern childGuard
    simpa only [d1857, d1715, d1701, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4583 (pattern : Twelve) (guard : d1857 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1702 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1715, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4580 pattern childGuard
    simpa only [d1857, d1715, d1702, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1715, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1857, d1715, d1702, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4584 (pattern : Twelve) (guard : d1857 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1703 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4582 pattern childGuard
    simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4583 pattern childGuard
    simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4585 (pattern : Twelve) (guard : d1857 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1704 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4571 pattern childGuard
    simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4584 pattern childGuard
    simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4586 (pattern : Twelve) (guard : d1848 pattern = 1) : d91 pattern ≤ (0 : Int) + d91 pattern := by
  omega
theorem c4587 (pattern : Twelve) (guard : d1869 pattern = 1) : d352 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d352, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4586 pattern childGuard
    simpa only [d1869, d352, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d352, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4319 pattern childGuard
    simpa only [d1869, d352, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4588 (pattern : Twelve) (guard : d1848 pattern = 1) : d93 pattern ≤ (0 : Int) + d93 pattern := by
  omega
theorem c4589 (pattern : Twelve) (guard : d1869 pattern = 1) : d353 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d353, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4588 pattern childGuard
    simpa only [d1869, d353, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d353, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4321 pattern childGuard
    simpa only [d1869, d353, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4590 (pattern : Twelve) (guard : d1869 pattern = 1) : d358 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d358, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4587 pattern childGuard
    simpa only [d358, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d358, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4589 pattern childGuard
    simpa only [d358, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4591 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4592 (pattern : Twelve) (guard : d1848 pattern = 1) : d27 pattern ≤ (0 : Int) + d37 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d27, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d27, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d27, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4591 pattern childGuard
    simpa only [d1848, d27, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4593 (pattern : Twelve) (guard : d1848 pattern = 1) : d50 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4407 pattern childGuard
    simpa only [d50, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4592 pattern childGuard
    simpa only [d50, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4594 (pattern : Twelve) (guard : d1848 pattern = 1) : d72 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4403 pattern childGuard
    simpa only [d72, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4593 pattern childGuard
    simpa only [d72, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4595 (pattern : Twelve) (guard : d1848 pattern = 1) : d51 pattern ≤ (0 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d51, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4414 pattern childGuard
    simpa only [d51, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d51, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d51, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4596 (pattern : Twelve) (guard : d1848 pattern = 1) : d73 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d73, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4403 pattern childGuard
    simpa only [d73, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d73, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4595 pattern childGuard
    simpa only [d73, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4597 (pattern : Twelve) (guard : d1848 pattern = 1) : d91 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d91, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4594 pattern childGuard
    simpa only [d91, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d91, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4596 pattern childGuard
    simpa only [d91, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4598 (pattern : Twelve) (guard : d0 pattern = 1) : d211 pattern ≤ (0 : Int) + d96 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4599 (pattern : Twelve) (guard : d1869 pattern = 1) : d354 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d354, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4597 pattern childGuard
    simpa only [d1869, d354, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d354, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4598 pattern childGuard
    simpa only [d1869, d354, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4600 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4403 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1354 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4601 (pattern : Twelve) (guard : d1848 pattern = 1) : d50 pattern ≤ (0 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4407 pattern childGuard
    simpa only [d50, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1415 pattern childGuard
    simpa only [d50, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4602 (pattern : Twelve) (guard : d1848 pattern = 1) : d72 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4600 pattern childGuard
    simpa only [d72, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4601 pattern childGuard
    simpa only [d72, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4603 (pattern : Twelve) (guard : d1848 pattern = 1) : d55 pattern ≤ (0 : Int) + d55 pattern := by
  omega
theorem c4604 (pattern : Twelve) (guard : d1848 pattern = 1) : d76 pattern ≤ (0 : Int) + d78 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d76, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4600 pattern childGuard
    simpa only [d76, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d76, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4603 pattern childGuard
    simpa only [d76, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4605 (pattern : Twelve) (guard : d1848 pattern = 1) : d93 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d93, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4602 pattern childGuard
    simpa only [d93, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d93, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4604 pattern childGuard
    simpa only [d93, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4606 (pattern : Twelve) (guard : d1869 pattern = 1) : d355 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d355, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4605 pattern childGuard
    simpa only [d1869, d355, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d355, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d355, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4607 (pattern : Twelve) (guard : d1869 pattern = 1) : d359 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d359, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4599 pattern childGuard
    simpa only [d359, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d359, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4606 pattern childGuard
    simpa only [d359, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4608 (pattern : Twelve) (guard : d1869 pattern = 1) : d361 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d361, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4590 pattern childGuard
    simpa only [d361, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d361, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4607 pattern childGuard
    simpa only [d361, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4609 (pattern : Twelve) (guard : d1848 pattern = 1) : d72 pattern ≤ (0 : Int) + d72 pattern := by
  omega
theorem c4610 (pattern : Twelve) (guard : d1848 pattern = 1) : d55 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d55, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1855 pattern childGuard
    simpa only [d55, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d55, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d55, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4611 (pattern : Twelve) (guard : d1848 pattern = 1) : d80 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1610 pattern childGuard
    simpa only [d80, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4610 pattern childGuard
    simpa only [d80, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4612 (pattern : Twelve) (guard : d1848 pattern = 1) : d97 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d97, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4609 pattern childGuard
    simpa only [d97, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d97, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4611 pattern childGuard
    simpa only [d97, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4613 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d356, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4612 pattern childGuard
    simpa only [d1869, d356, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d356, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4334 pattern childGuard
    simpa only [d1869, d356, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4614 (pattern : Twelve) (guard : d1848 pattern = 1) : d80 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1610 pattern childGuard
    simpa only [d80, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4603 pattern childGuard
    simpa only [d80, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4615 (pattern : Twelve) (guard : d1848 pattern = 1) : d97 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d97, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4609 pattern childGuard
    simpa only [d97, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d97, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4614 pattern childGuard
    simpa only [d97, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4616 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d356, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4615 pattern childGuard
    simpa only [d1869, d356, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d356, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4336 pattern childGuard
    simpa only [d1869, d356, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4617 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4613 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4616 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4618 (pattern : Twelve) (guard : d1848 pattern = 1) : d80 pattern ≤ (0 : Int) + d80 pattern := by
  omega
theorem c4619 (pattern : Twelve) (guard : d1848 pattern = 1) : d97 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d97, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4594 pattern childGuard
    simpa only [d97, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d97, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4618 pattern childGuard
    simpa only [d97, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
