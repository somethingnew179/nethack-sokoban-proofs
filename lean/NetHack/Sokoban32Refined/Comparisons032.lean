/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons031
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4480 (p : Pattern) (guard : d1293 p = 1) : d14 p ≤ (0 : Int) + d698 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4478 p hg
    simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4479 p hg
    simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4481 (p : Pattern) (guard : d1293 p = 1) : d15 p ≤ (0 : Int) + d699 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4475 p hg
    simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4480 p hg
    simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4482 (p : Pattern) (guard : d1293 p = 1) : d16 p ≤ (0 : Int) + d700 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4475 p hg
    simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4483 (p : Pattern) (guard : d1294 p = 1) : d16 p ≤ (0 : Int) + d700 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3417 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4482 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4484 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4485 (p : Pattern) (guard : d985 p = 1) : d3 p ≤ (0 : Int) + d0 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare103 p hg
    simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4484 p hg
    simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4486 (p : Pattern) (guard : d1293 p = 1) : d17 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d17, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d1293, d17, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d17, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1293, d17, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4487 (p : Pattern) (guard : d1293 p = 1) : d18 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4470 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4486 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4488 (p : Pattern) (guard : d1293 p = 1) : d19 p ≤ (0 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d19, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4486 p hg
    simpa only [d19, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d19, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d19, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4489 (p : Pattern) (guard : d1293 p = 1) : d20 p ≤ (0 : Int) + d697 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d20, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d20, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d20, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4488 p hg
    simpa only [d20, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4490 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4491 (p : Pattern) (guard : d985 p = 1) : d9 p ≤ (0 : Int) + d1 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare698 p hg
    simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4490 p hg
    simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4492 (p : Pattern) (guard : d1293 p = 1) : d21 p ≤ (0 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4491 p hg
    simpa only [d1293, d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1293, d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4493 (p : Pattern) (guard : d1293 p = 1) : d22 p ≤ (0 : Int) + d11 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4476 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4492 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4494 (p : Pattern) (guard : d1293 p = 1) : d23 p ≤ (0 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4492 p hg
    simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4495 (p : Pattern) (guard : d1293 p = 1) : d24 p ≤ (0 : Int) + d698 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d24, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d24, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d24, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4494 p hg
    simpa only [d24, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4496 (p : Pattern) (guard : d1293 p = 1) : d25 p ≤ (0 : Int) + d699 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d25, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4489 p hg
    simpa only [d25, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d25, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4495 p hg
    simpa only [d25, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4497 (p : Pattern) (guard : d1293 p = 1) : d26 p ≤ (0 : Int) + d700 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d26, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4489 p hg
    simpa only [d26, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d26, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4496 p hg
    simpa only [d26, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4498 (p : Pattern) (guard : d1294 p = 1) : d27 p ≤ (0 : Int) + d700 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3417 p hg
    simpa only [d1294, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d1294, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4499 (p : Pattern) (guard : d1294 p = 1) : d28 p ≤ (0 : Int) + d700 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4483 p hg
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4498 p hg
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4500 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4501 (p : Pattern) (guard : d985 p = 1) : d29 p ≤ (0 : Int) + d0 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare103 p hg
    simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4500 p hg
    simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4502 (p : Pattern) (guard : d1293 p = 1) : d30 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d30, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4501 p hg
    simpa only [d1293, d30, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d30, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1293, d30, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4503 (p : Pattern) (guard : d1293 p = 1) : d31 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4470 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4502 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4504 (p : Pattern) (guard : d1293 p = 1) : d32 p ≤ (0 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d32, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4502 p hg
    simpa only [d32, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d32, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d32, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4505 (p : Pattern) (guard : d1293 p = 1) : d33 p ≤ (0 : Int) + d697 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d33, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4503 p hg
    simpa only [d33, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d33, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4504 p hg
    simpa only [d33, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4506 (p : Pattern) (guard : d1293 p = 1) : d34 p ≤ (0 : Int) + d699 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d34, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4505 p hg
    simpa only [d34, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d34, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4495 p hg
    simpa only [d34, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4507 (p : Pattern) (guard : d1293 p = 1) : d35 p ≤ (0 : Int) + d700 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d35, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4505 p hg
    simpa only [d35, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d35, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4506 p hg
    simpa only [d35, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4508 (p : Pattern) (guard : d1294 p = 1) : d36 p ≤ (0 : Int) + d700 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3417 p hg
    simpa only [d1294, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4507 p hg
    simpa only [d1294, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4509 (p : Pattern) (guard : d1294 p = 1) : d43 p ≤ (0 : Int) + d700 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3743 p hg
    simpa only [d1294, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d1294, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4510 (p : Pattern) (guard : d1294 p = 1) : d44 p ≤ (0 : Int) + d700 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4508 p hg
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4509 p hg
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4511 (p : Pattern) (guard : d1294 p = 1) : d45 p ≤ (0 : Int) + d700 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4499 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4510 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4512 (p : Pattern) (guard : d1294 p = 1) : d15 p ≤ (0 : Int) + d699 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3416 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4513 (p : Pattern) (guard : d1294 p = 1) : d46 p ≤ (0 : Int) + d699 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3416 p hg
    simpa only [d1294, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4496 p hg
    simpa only [d1294, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4514 (p : Pattern) (guard : d1294 p = 1) : d47 p ≤ (0 : Int) + d699 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4512 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4513 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4515 (p : Pattern) (guard : d1294 p = 1) : d48 p ≤ (0 : Int) + d699 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3416 p hg
    simpa only [d1294, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4506 p hg
    simpa only [d1294, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4516 (p : Pattern) (guard : d1294 p = 1) : d49 p ≤ (0 : Int) + d699 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3742 p hg
    simpa only [d1294, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4496 p hg
    simpa only [d1294, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4517 (p : Pattern) (guard : d1294 p = 1) : d50 p ≤ (0 : Int) + d699 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4518 (p : Pattern) (guard : d1294 p = 1) : d51 p ≤ (0 : Int) + d699 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4514 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4519 (p : Pattern) (guard : d1293 p = 1) : d52 p ≤ (0 : Int) + d701 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4475 p hg
    simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4520 (p : Pattern) (guard : d1293 p = 1) : d53 p ≤ (0 : Int) + d702 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4521 (p : Pattern) (guard : d1294 p = 1) : d53 p ≤ (0 : Int) + d702 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3435 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4520 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4522 (p : Pattern) (guard : d1293 p = 1) : d54 p ≤ (0 : Int) + d701 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d54, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4489 p hg
    simpa only [d54, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d54, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d54, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4523 (p : Pattern) (guard : d1293 p = 1) : d55 p ≤ (0 : Int) + d702 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d55, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4496 p hg
    simpa only [d55, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d55, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4522 p hg
    simpa only [d55, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4524 (p : Pattern) (guard : d1294 p = 1) : d56 p ≤ (0 : Int) + d702 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3435 p hg
    simpa only [d1294, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1294, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4525 (p : Pattern) (guard : d1294 p = 1) : d57 p ≤ (0 : Int) + d702 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4521 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4524 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4526 (p : Pattern) (guard : d1293 p = 1) : d58 p ≤ (0 : Int) + d701 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d58, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4505 p hg
    simpa only [d58, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d58, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d58, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4527 (p : Pattern) (guard : d1293 p = 1) : d59 p ≤ (0 : Int) + d702 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d59, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4506 p hg
    simpa only [d59, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d59, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4526 p hg
    simpa only [d59, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4528 (p : Pattern) (guard : d1294 p = 1) : d60 p ≤ (0 : Int) + d702 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3435 p hg
    simpa only [d1294, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4527 p hg
    simpa only [d1294, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4529 (p : Pattern) (guard : d1294 p = 1) : d63 p ≤ (0 : Int) + d702 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3753 p hg
    simpa only [d1294, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1294, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4530 (p : Pattern) (guard : d1294 p = 1) : d64 p ≤ (0 : Int) + d702 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4528 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4529 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4531 (p : Pattern) (guard : d1294 p = 1) : d65 p ≤ (0 : Int) + d702 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4525 p hg
    simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4530 p hg
    simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4532 (p : Pattern) (guard : d1294 p = 1) : d66 p ≤ (0 : Int) + d703 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d66, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d66, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d66, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d66, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4533 (p : Pattern) (guard : d1294 p = 1) : d67 p ≤ (0 : Int) + d704 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d67, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4511 p hg
    simpa only [d67, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d67, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4532 p hg
    simpa only [d67, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4534 (p : Pattern) (guard : d1293 p = 1) : d70 p ≤ (0 : Int) + d705 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d70, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4495 p hg
    simpa only [d70, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d70, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d70, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4535 (p : Pattern) (guard : d1293 p = 1) : d71 p ≤ (0 : Int) + d706 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d71, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4495 p hg
    simpa only [d71, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d71, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4534 p hg
    simpa only [d71, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4536 (p : Pattern) (guard : d1294 p = 1) : d72 p ≤ (0 : Int) + d706 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3760 p hg
    simpa only [d1294, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4535 p hg
    simpa only [d1294, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4537 (p : Pattern) (guard : d1294 p = 1) : d73 p ≤ (0 : Int) + d707 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d73, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4498 p hg
    simpa only [d73, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d73, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4536 p hg
    simpa only [d73, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4538 (p : Pattern) (guard : d1294 p = 1) : d74 p ≤ (0 : Int) + d708 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d74, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4499 p hg
    simpa only [d74, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d74, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4537 p hg
    simpa only [d74, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4539 (p : Pattern) (guard : d1294 p = 1) : d75 p ≤ (0 : Int) + d705 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3759 p hg
    simpa only [d1294, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4534 p hg
    simpa only [d1294, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4540 (p : Pattern) (guard : d1294 p = 1) : d76 p ≤ (0 : Int) + d709 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d76, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4498 p hg
    simpa only [d76, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d76, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4539 p hg
    simpa only [d76, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4541 (p : Pattern) (guard : d1294 p = 1) : d77 p ≤ (0 : Int) + d710 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d77, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4499 p hg
    simpa only [d77, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d77, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4540 p hg
    simpa only [d77, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4542 (p : Pattern) (guard : d1294 p = 1) : d78 p ≤ (0 : Int) + d711 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d78, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4538 p hg
    simpa only [d78, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d78, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d78, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4543 (p : Pattern) (guard : d1294 p = 1) : d79 p ≤ (0 : Int) + d712 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d79, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4513 p hg
    simpa only [d79, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d79, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4539 p hg
    simpa only [d79, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4544 (p : Pattern) (guard : d1294 p = 1) : d80 p ≤ (0 : Int) + d713 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d80, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4514 p hg
    simpa only [d80, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d80, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4543 p hg
    simpa only [d80, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4545 (p : Pattern) (guard : d1294 p = 1) : d81 p ≤ (0 : Int) + d714 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d81, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4524 p hg
    simpa only [d81, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d81, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4539 p hg
    simpa only [d81, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4546 (p : Pattern) (guard : d1294 p = 1) : d82 p ≤ (0 : Int) + d715 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d82, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4525 p hg
    simpa only [d82, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d82, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4545 p hg
    simpa only [d82, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4547 (p : Pattern) (guard : d1294 p = 1) : d83 p ≤ (0 : Int) + d716 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d83, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4544 p hg
    simpa only [d83, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d83, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4546 p hg
    simpa only [d83, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4548 (p : Pattern) (guard : d1294 p = 1) : d84 p ≤ (0 : Int) + d717 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d84, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4542 p hg
    simpa only [d84, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d84, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4547 p hg
    simpa only [d84, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4549 (p : Pattern) (guard : d1294 p = 1) : d85 p ≤ (0 : Int) + d718 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d85, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4533 p hg
    simpa only [d85, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d85, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4548 p hg
    simpa only [d85, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4550 (p : Pattern) (guard : d1293 p = 1) : d86 p ≤ (0 : Int) + d719 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4475 p hg
    simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4551 (p : Pattern) (guard : d1294 p = 1) : d86 p ≤ (0 : Int) + d719 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3459 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4550 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4552 (p : Pattern) (guard : d1293 p = 1) : d87 p ≤ (0 : Int) + d719 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d87, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4489 p hg
    simpa only [d87, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d87, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4522 p hg
    simpa only [d87, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4553 (p : Pattern) (guard : d1294 p = 1) : d88 p ≤ (0 : Int) + d719 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3459 p hg
    simpa only [d1294, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4552 p hg
    simpa only [d1294, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4554 (p : Pattern) (guard : d1294 p = 1) : d89 p ≤ (0 : Int) + d719 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4551 p hg
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4553 p hg
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4555 (p : Pattern) (guard : d1293 p = 1) : d90 p ≤ (0 : Int) + d719 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d90, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4505 p hg
    simpa only [d90, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d90, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4526 p hg
    simpa only [d90, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4556 (p : Pattern) (guard : d1294 p = 1) : d91 p ≤ (0 : Int) + d719 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3459 p hg
    simpa only [d1294, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4555 p hg
    simpa only [d1294, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4557 (p : Pattern) (guard : d1294 p = 1) : d93 p ≤ (0 : Int) + d719 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3776 p hg
    simpa only [d1294, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4552 p hg
    simpa only [d1294, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4558 (p : Pattern) (guard : d1294 p = 1) : d94 p ≤ (0 : Int) + d719 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4557 p hg
    simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4559 (p : Pattern) (guard : d1294 p = 1) : d95 p ≤ (0 : Int) + d719 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4554 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4560 (p : Pattern) (guard : d1294 p = 1) : d96 p ≤ (0 : Int) + d720 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d96, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4511 p hg
    simpa only [d96, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d96, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4559 p hg
    simpa only [d96, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4561 (p : Pattern) (guard : d1293 p = 1) : d97 p ≤ (0 : Int) + d705 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4480 p hg
    simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4562 (p : Pattern) (guard : d1293 p = 1) : d98 p ≤ (0 : Int) + d706 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4480 p hg
    simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4561 p hg
    simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4563 (p : Pattern) (guard : d1294 p = 1) : d98 p ≤ (0 : Int) + d706 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3469 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4562 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4564 (p : Pattern) (guard : d1294 p = 1) : d99 p ≤ (0 : Int) + d706 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3469 p hg
    simpa only [d1294, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4535 p hg
    simpa only [d1294, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4565 (p : Pattern) (guard : d1294 p = 1) : d100 p ≤ (0 : Int) + d706 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4563 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4566 (p : Pattern) (guard : d1294 p = 1) : d101 p ≤ (0 : Int) + d706 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4536 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4567 (p : Pattern) (guard : d1294 p = 1) : d102 p ≤ (0 : Int) + d706 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4565 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4566 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4568 (p : Pattern) (guard : d1294 p = 1) : d103 p ≤ (0 : Int) + d721 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d103, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4560 p hg
    simpa only [d103, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d103, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4567 p hg
    simpa only [d103, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4569 (p : Pattern) (guard : d1294 p = 1) : d104 p ≤ (0 : Int) + d722 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d104, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4553 p hg
    simpa only [d104, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d104, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4539 p hg
    simpa only [d104, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4570 (p : Pattern) (guard : d1294 p = 1) : d105 p ≤ (0 : Int) + d723 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d105, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4554 p hg
    simpa only [d105, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d105, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4569 p hg
    simpa only [d105, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4571 (p : Pattern) (guard : d1294 p = 1) : d106 p ≤ (0 : Int) + d724 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d106, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d106, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d106, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4570 p hg
    simpa only [d106, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4572 (p : Pattern) (guard : d1294 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare4573 (p : Pattern) (guard : d1294 p = 1) : d107 p ≤ (0 : Int) + d725 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d107, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d107, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d107, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4572 p hg
    simpa only [d107, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4574 (p : Pattern) (guard : d1294 p = 1) : d108 p ≤ (0 : Int) + d726 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d108, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4565 p hg
    simpa only [d108, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d108, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4573 p hg
    simpa only [d108, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4575 (p : Pattern) (guard : d1294 p = 1) : d97 p ≤ (0 : Int) + d705 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3468 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4561 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4576 (p : Pattern) (guard : d1294 p = 1) : d109 p ≤ (0 : Int) + d705 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3468 p hg
    simpa only [d1294, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4534 p hg
    simpa only [d1294, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4577 (p : Pattern) (guard : d1294 p = 1) : d110 p ≤ (0 : Int) + d705 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4575 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4576 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4578 (p : Pattern) (guard : d1294 p = 1) : d111 p ≤ (0 : Int) + d727 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d111, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4576 p hg
    simpa only [d111, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d111, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4572 p hg
    simpa only [d111, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4579 (p : Pattern) (guard : d1294 p = 1) : d112 p ≤ (0 : Int) + d728 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d112, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4577 p hg
    simpa only [d112, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d112, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4578 p hg
    simpa only [d112, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4580 (p : Pattern) (guard : d1294 p = 1) : d113 p ≤ (0 : Int) + d729 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d113, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4574 p hg
    simpa only [d113, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d113, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4579 p hg
    simpa only [d113, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4581 (p : Pattern) (guard : d1294 p = 1) : d114 p ≤ (0 : Int) + d730 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d114, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4571 p hg
    simpa only [d114, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d114, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4580 p hg
    simpa only [d114, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4582 (p : Pattern) (guard : d1294 p = 1) : d115 p ≤ (0 : Int) + d731 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d115, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d115, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d115, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4581 p hg
    simpa only [d115, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4583 (p : Pattern) (guard : d1294 p = 1) : d116 p ≤ (0 : Int) + d732 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d116, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d116, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d116, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4582 p hg
    simpa only [d116, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4584 (p : Pattern) (guard : d1294 p = 1) : d117 p ≤ (0 : Int) + d733 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d117, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d117, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d117, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4547 p hg
    simpa only [d117, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4585 (p : Pattern) (guard : d1294 p = 1) : d118 p ≤ (0 : Int) + d734 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d118, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4533 p hg
    simpa only [d118, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d118, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4584 p hg
    simpa only [d118, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4586 (p : Pattern) (guard : d1293 p = 1) : d119 p ≤ (0 : Int) + d697 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4505 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4489 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4587 (p : Pattern) (guard : d1293 p = 1) : d120 p ≤ (0 : Int) + d719 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d120, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4586 p hg
    simpa only [d120, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d120, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4526 p hg
    simpa only [d120, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4588 (p : Pattern) (guard : d1294 p = 1) : d121 p ≤ (0 : Int) + d719 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3459 p hg
    simpa only [d1294, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4587 p hg
    simpa only [d1294, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4589 (p : Pattern) (guard : d1294 p = 1) : d122 p ≤ (0 : Int) + d719 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4588 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4557 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4590 (p : Pattern) (guard : d1294 p = 1) : d123 p ≤ (0 : Int) + d719 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4554 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4589 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4591 (p : Pattern) (guard : d1294 p = 1) : d124 p ≤ (0 : Int) + d720 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d124, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4511 p hg
    simpa only [d124, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d124, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4590 p hg
    simpa only [d124, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4592 (p : Pattern) (guard : d1294 p = 1) : d125 p ≤ (0 : Int) + d705 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4576 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4539 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4593 (p : Pattern) (guard : d1294 p = 1) : d126 p ≤ (0 : Int) + d705 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4577 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4592 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4594 (p : Pattern) (guard : d1294 p = 1) : d127 p ≤ (0 : Int) + d735 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d127, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4567 p hg
    simpa only [d127, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d127, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4593 p hg
    simpa only [d127, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4595 (p : Pattern) (guard : d1294 p = 1) : d128 p ≤ (0 : Int) + d736 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d128, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4591 p hg
    simpa only [d128, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d128, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4594 p hg
    simpa only [d128, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4596 (p : Pattern) (guard : d1294 p = 1) : d129 p ≤ (0 : Int) + d737 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d129, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d129, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d129, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4546 p hg
    simpa only [d129, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4597 (p : Pattern) (guard : d1294 p = 1) : d130 p ≤ (0 : Int) + d738 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d130, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4579 p hg
    simpa only [d130, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d130, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4572 p hg
    simpa only [d130, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4598 (p : Pattern) (guard : d1294 p = 1) : d131 p ≤ (0 : Int) + d739 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d131, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4596 p hg
    simpa only [d131, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d131, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4597 p hg
    simpa only [d131, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4599 (p : Pattern) (guard : d1294 p = 1) : d132 p ≤ (0 : Int) + d740 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d132, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4595 p hg
    simpa only [d132, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d132, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4598 p hg
    simpa only [d132, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4600 (p : Pattern) (guard : d1294 p = 1) : d133 p ≤ (0 : Int) + d741 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d133, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4585 p hg
    simpa only [d133, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d133, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4599 p hg
    simpa only [d133, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4601 (p : Pattern) (guard : d1294 p = 1) : d134 p ≤ (0 : Int) + d742 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d134, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4583 p hg
    simpa only [d134, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d134, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4600 p hg
    simpa only [d134, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4602 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (2 : Int) + d8 p := by
  omega
theorem compare4603 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (2 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4350 p hg
    simpa only [d5, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d5, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4604 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4352 p hg
    simpa only [d6, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4603 p hg
    simpa only [d6, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4605 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (2 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4352 p hg
    simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4606 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (2 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4604 p hg
    simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4605 p hg
    simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4607 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (2 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4602 p hg
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4606 p hg
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4608 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (2 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4609 (p : Pattern) (guard : d857 p = 1) : d16 p ≤ (2 : Int) + d15 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4607 p hg
    simpa only [d857, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4608 p hg
    simpa only [d857, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4610 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (2 : Int) + d20 p := by
  omega
theorem compare4611 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (2 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4351 p hg
    simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4612 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d22 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4352 p hg
    simpa only [d18, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4611 p hg
    simpa only [d18, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4613 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (2 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4611 p hg
    simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4614 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (2 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4612 p hg
    simpa only [d20, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4613 p hg
    simpa only [d20, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4615 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (2 : Int) + d25 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4610 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4614 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4616 (p : Pattern) (guard : d0 p = 1) : d25 p ≤ (2 : Int) + d25 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4617 (p : Pattern) (guard : d857 p = 1) : d26 p ≤ (2 : Int) + d25 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4615 p hg
    simpa only [d857, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4616 p hg
    simpa only [d857, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4618 (p : Pattern) (guard : d857 p = 1) : d27 p ≤ (2 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d27, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4609 p hg
    simpa only [d27, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d27, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4617 p hg
    simpa only [d27, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4619 (p : Pattern) (guard : d857 p = 1) : d28 p ≤ (2 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d28, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4609 p hg
    simpa only [d28, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d28, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4618 p hg
    simpa only [d28, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
