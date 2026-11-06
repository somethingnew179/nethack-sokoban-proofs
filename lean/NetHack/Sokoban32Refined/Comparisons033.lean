/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons032
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4620 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (2 : Int) + d33 p := by
  omega
theorem compare4621 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (2 : Int) + d9 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4350 p hg
    simpa only [d29, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4358 p hg
    simpa only [d29, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4622 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (2 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4621 p hg
    simpa only [d30, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d30, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4623 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d22 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4352 p hg
    simpa only [d31, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4622 p hg
    simpa only [d31, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4624 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (2 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4622 p hg
    simpa only [d32, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d32, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4625 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (2 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4623 p hg
    simpa only [d33, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4624 p hg
    simpa only [d33, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4626 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (2 : Int) + d34 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4620 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4625 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4627 (p : Pattern) (guard : d0 p = 1) : d34 p ≤ (2 : Int) + d34 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4628 (p : Pattern) (guard : d857 p = 1) : d35 p ≤ (2 : Int) + d34 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4626 p hg
    simpa only [d857, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4627 p hg
    simpa only [d857, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4629 (p : Pattern) (guard : d857 p = 1) : d36 p ≤ (2 : Int) + d48 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d36, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4609 p hg
    simpa only [d36, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d36, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4628 p hg
    simpa only [d36, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4630 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (2 : Int) + d38 p := by
  omega
theorem compare4631 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (2 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4603 p hg
    simpa only [d37, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d37, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4632 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (2 : Int) + d40 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4604 p hg
    simpa only [d38, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4631 p hg
    simpa only [d38, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4633 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (2 : Int) + d41 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4632 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4634 (p : Pattern) (guard : d0 p = 1) : d41 p ≤ (2 : Int) + d41 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4635 (p : Pattern) (guard : d857 p = 1) : d42 p ≤ (2 : Int) + d41 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4633 p hg
    simpa only [d857, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4634 p hg
    simpa only [d857, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4636 (p : Pattern) (guard : d857 p = 1) : d43 p ≤ (2 : Int) + d49 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d43, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4635 p hg
    simpa only [d43, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d43, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4617 p hg
    simpa only [d43, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4637 (p : Pattern) (guard : d857 p = 1) : d44 p ≤ (2 : Int) + d50 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d44, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4629 p hg
    simpa only [d44, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d44, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4636 p hg
    simpa only [d44, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4638 (p : Pattern) (guard : d857 p = 1) : d45 p ≤ (2 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d45, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4619 p hg
    simpa only [d45, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d45, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4637 p hg
    simpa only [d45, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4639 (p : Pattern) (guard : d857 p = 1) : d51 p ≤ (2 : Int) + d51 p := by
  omega
theorem compare4640 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4358 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4641 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4360 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4640 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4642 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4360 p hg
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4643 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4641 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4642 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4644 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (2 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4602 p hg
    simpa only [d15, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4643 p hg
    simpa only [d15, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4645 (p : Pattern) (guard : d0 p = 1) : d52 p ≤ (2 : Int) + d52 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4646 (p : Pattern) (guard : d857 p = 1) : d53 p ≤ (2 : Int) + d52 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4644 p hg
    simpa only [d857, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4645 p hg
    simpa only [d857, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4647 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (2 : Int) + d54 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4610 p hg
    simpa only [d25, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4364 p hg
    simpa only [d25, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4648 (p : Pattern) (guard : d0 p = 1) : d54 p ≤ (2 : Int) + d54 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4649 (p : Pattern) (guard : d857 p = 1) : d55 p ≤ (2 : Int) + d54 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4647 p hg
    simpa only [d857, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4648 p hg
    simpa only [d857, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4650 (p : Pattern) (guard : d857 p = 1) : d56 p ≤ (2 : Int) + d470 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d56, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4646 p hg
    simpa only [d56, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d56, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4649 p hg
    simpa only [d56, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4651 (p : Pattern) (guard : d857 p = 1) : d57 p ≤ (2 : Int) + d524 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d57, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4646 p hg
    simpa only [d57, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d57, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4650 p hg
    simpa only [d57, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4652 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (2 : Int) + d58 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4620 p hg
    simpa only [d34, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4364 p hg
    simpa only [d34, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4653 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (2 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4654 (p : Pattern) (guard : d857 p = 1) : d59 p ≤ (2 : Int) + d58 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4652 p hg
    simpa only [d857, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4653 p hg
    simpa only [d857, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4655 (p : Pattern) (guard : d857 p = 1) : d60 p ≤ (2 : Int) + d519 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d60, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4646 p hg
    simpa only [d60, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d60, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4654 p hg
    simpa only [d60, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4656 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4640 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4657 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (2 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4641 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4656 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4658 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (2 : Int) + d61 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d41, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4657 p hg
    simpa only [d41, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4659 (p : Pattern) (guard : d0 p = 1) : d61 p ≤ (2 : Int) + d61 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4660 (p : Pattern) (guard : d857 p = 1) : d62 p ≤ (2 : Int) + d61 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4658 p hg
    simpa only [d857, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4659 p hg
    simpa only [d857, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4661 (p : Pattern) (guard : d857 p = 1) : d63 p ≤ (2 : Int) + d473 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d63, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4660 p hg
    simpa only [d63, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d63, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4649 p hg
    simpa only [d63, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4662 (p : Pattern) (guard : d857 p = 1) : d64 p ≤ (2 : Int) + d520 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d64, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4655 p hg
    simpa only [d64, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d64, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4661 p hg
    simpa only [d64, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4663 (p : Pattern) (guard : d857 p = 1) : d65 p ≤ (2 : Int) + d1295 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d65, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4651 p hg
    simpa only [d65, d1295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d65, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4662 p hg
    simpa only [d65, d1295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4664 (p : Pattern) (guard : d857 p = 1) : d66 p ≤ (2 : Int) + d1296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d66, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4639 p hg
    simpa only [d66, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d66, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4663 p hg
    simpa only [d66, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4665 (p : Pattern) (guard : d857 p = 1) : d67 p ≤ (2 : Int) + d1297 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d67, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4638 p hg
    simpa only [d67, d1297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d67, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4664 p hg
    simpa only [d67, d1297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4666 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (2 : Int) + d40 p := by
  omega
theorem compare4667 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (2 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4666 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4657 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4668 (p : Pattern) (guard : d0 p = 1) : d68 p ≤ (2 : Int) + d68 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4669 (p : Pattern) (guard : d857 p = 1) : d69 p ≤ (2 : Int) + d68 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4667 p hg
    simpa only [d857, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4668 p hg
    simpa only [d857, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4670 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (2 : Int) + d24 p := by
  omega
theorem compare4671 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (2 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4670 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4364 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4672 (p : Pattern) (guard : d0 p = 1) : d70 p ≤ (2 : Int) + d70 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4673 (p : Pattern) (guard : d857 p = 1) : d71 p ≤ (2 : Int) + d70 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4671 p hg
    simpa only [d857, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4672 p hg
    simpa only [d857, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4674 (p : Pattern) (guard : d857 p = 1) : d72 p ≤ (2 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d72, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4669 p hg
    simpa only [d72, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d72, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4673 p hg
    simpa only [d72, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4675 (p : Pattern) (guard : d857 p = 1) : d73 p ≤ (2 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d73, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4618 p hg
    simpa only [d73, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d73, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4674 p hg
    simpa only [d73, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4676 (p : Pattern) (guard : d857 p = 1) : d74 p ≤ (2 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d74, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4619 p hg
    simpa only [d74, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d74, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4675 p hg
    simpa only [d74, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4677 (p : Pattern) (guard : d857 p = 1) : d75 p ≤ (2 : Int) + d75 p := by
  omega
theorem compare4678 (p : Pattern) (guard : d857 p = 1) : d76 p ≤ (2 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d76, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4618 p hg
    simpa only [d76, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d76, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4677 p hg
    simpa only [d76, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4679 (p : Pattern) (guard : d857 p = 1) : d77 p ≤ (2 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d77, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4619 p hg
    simpa only [d77, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d77, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4678 p hg
    simpa only [d77, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4680 (p : Pattern) (guard : d857 p = 1) : d78 p ≤ (2 : Int) + d80 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4676 p hg
    simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4679 p hg
    simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4681 (p : Pattern) (guard : d857 p = 1) : d80 p ≤ (2 : Int) + d80 p := by
  omega
theorem compare4682 (p : Pattern) (guard : d857 p = 1) : d81 p ≤ (2 : Int) + d491 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d81, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4650 p hg
    simpa only [d81, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d81, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4677 p hg
    simpa only [d81, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4683 (p : Pattern) (guard : d857 p = 1) : d82 p ≤ (2 : Int) + d525 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d82, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4651 p hg
    simpa only [d82, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d82, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4682 p hg
    simpa only [d82, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4684 (p : Pattern) (guard : d857 p = 1) : d83 p ≤ (2 : Int) + d1298 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d83, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4681 p hg
    simpa only [d83, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d83, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4683 p hg
    simpa only [d83, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4685 (p : Pattern) (guard : d857 p = 1) : d84 p ≤ (2 : Int) + d1299 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d84, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4680 p hg
    simpa only [d84, d1299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d84, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4684 p hg
    simpa only [d84, d1299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4686 (p : Pattern) (guard : d857 p = 1) : d85 p ≤ (2 : Int) + d1300 p := by
  cases selected : p 106 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d85, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4665 p hg
    simpa only [d85, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d85, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4685 p hg
    simpa only [d85, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4687 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4372 p hg
    simpa only [d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4688 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4374 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4687 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4689 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4374 p hg
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4690 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (2 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4689 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4691 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (2 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4602 p hg
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4690 p hg
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4692 (p : Pattern) (guard : d857 p = 1) : d86 p ≤ (2 : Int) + d52 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4691 p hg
    simpa only [d857, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4645 p hg
    simpa only [d857, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4693 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (2 : Int) + d54 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4610 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4378 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4694 (p : Pattern) (guard : d857 p = 1) : d87 p ≤ (2 : Int) + d54 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4693 p hg
    simpa only [d857, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4648 p hg
    simpa only [d857, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4695 (p : Pattern) (guard : d857 p = 1) : d88 p ≤ (2 : Int) + d470 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d88, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4692 p hg
    simpa only [d88, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d88, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4694 p hg
    simpa only [d88, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4696 (p : Pattern) (guard : d857 p = 1) : d89 p ≤ (2 : Int) + d524 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d89, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4692 p hg
    simpa only [d89, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d89, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4695 p hg
    simpa only [d89, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4697 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (2 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4372 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4358 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4698 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4697 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4699 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4374 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4698 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4700 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4698 p hg
    simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4701 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (2 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4699 p hg
    simpa only [d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4700 p hg
    simpa only [d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4702 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (2 : Int) + d58 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4620 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4701 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4703 (p : Pattern) (guard : d857 p = 1) : d90 p ≤ (2 : Int) + d58 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4702 p hg
    simpa only [d857, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4653 p hg
    simpa only [d857, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4704 (p : Pattern) (guard : d857 p = 1) : d91 p ≤ (2 : Int) + d519 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d91, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4692 p hg
    simpa only [d91, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d91, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4703 p hg
    simpa only [d91, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4705 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4687 p hg
    simpa only [d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4706 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (2 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4705 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4707 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (2 : Int) + d61 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4706 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4708 (p : Pattern) (guard : d857 p = 1) : d92 p ≤ (2 : Int) + d61 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4707 p hg
    simpa only [d857, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4659 p hg
    simpa only [d857, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4709 (p : Pattern) (guard : d857 p = 1) : d93 p ≤ (2 : Int) + d473 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d93, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4708 p hg
    simpa only [d93, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d93, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4694 p hg
    simpa only [d93, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4710 (p : Pattern) (guard : d857 p = 1) : d94 p ≤ (2 : Int) + d520 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d94, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4704 p hg
    simpa only [d94, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d94, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4709 p hg
    simpa only [d94, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4711 (p : Pattern) (guard : d857 p = 1) : d95 p ≤ (2 : Int) + d1295 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d95, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4696 p hg
    simpa only [d95, d1295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d95, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4710 p hg
    simpa only [d95, d1295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4712 (p : Pattern) (guard : d857 p = 1) : d96 p ≤ (2 : Int) + d1296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d96, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4638 p hg
    simpa only [d96, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d96, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4711 p hg
    simpa only [d96, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4713 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d14 p := by
  omega
theorem compare4714 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4713 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4643 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4715 (p : Pattern) (guard : d0 p = 1) : d97 p ≤ (2 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4716 (p : Pattern) (guard : d857 p = 1) : d98 p ≤ (2 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4714 p hg
    simpa only [d857, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4715 p hg
    simpa only [d857, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4717 (p : Pattern) (guard : d857 p = 1) : d99 p ≤ (2 : Int) + d109 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d99, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4716 p hg
    simpa only [d99, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d99, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4673 p hg
    simpa only [d99, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4718 (p : Pattern) (guard : d857 p = 1) : d100 p ≤ (2 : Int) + d110 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d100, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4716 p hg
    simpa only [d100, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d100, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4717 p hg
    simpa only [d100, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4719 (p : Pattern) (guard : d857 p = 1) : d101 p ≤ (2 : Int) + d125 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d101, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4717 p hg
    simpa only [d101, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d101, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4674 p hg
    simpa only [d101, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4720 (p : Pattern) (guard : d857 p = 1) : d102 p ≤ (2 : Int) + d126 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d102, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4718 p hg
    simpa only [d102, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d102, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4719 p hg
    simpa only [d102, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4721 (p : Pattern) (guard : d857 p = 1) : d103 p ≤ (2 : Int) + d1301 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d103, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4712 p hg
    simpa only [d103, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d103, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4720 p hg
    simpa only [d103, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4722 (p : Pattern) (guard : d857 p = 1) : d104 p ≤ (2 : Int) + d491 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d104, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4695 p hg
    simpa only [d104, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d104, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4677 p hg
    simpa only [d104, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4723 (p : Pattern) (guard : d857 p = 1) : d105 p ≤ (2 : Int) + d525 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d105, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4696 p hg
    simpa only [d105, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d105, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4722 p hg
    simpa only [d105, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4724 (p : Pattern) (guard : d857 p = 1) : d106 p ≤ (2 : Int) + d1298 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d106, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4679 p hg
    simpa only [d106, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d106, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4723 p hg
    simpa only [d106, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4725 (p : Pattern) (guard : d857 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  omega
theorem compare4726 (p : Pattern) (guard : d857 p = 1) : d107 p ≤ (2 : Int) + d111 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d107, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4717 p hg
    simpa only [d107, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d107, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4725 p hg
    simpa only [d107, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4727 (p : Pattern) (guard : d857 p = 1) : d108 p ≤ (2 : Int) + d112 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d108, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4718 p hg
    simpa only [d108, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d108, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4726 p hg
    simpa only [d108, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4728 (p : Pattern) (guard : d857 p = 1) : d112 p ≤ (2 : Int) + d112 p := by
  omega
theorem compare4729 (p : Pattern) (guard : d857 p = 1) : d113 p ≤ (2 : Int) + d112 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4727 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4728 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4730 (p : Pattern) (guard : d857 p = 1) : d114 p ≤ (2 : Int) + d1302 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d114, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4724 p hg
    simpa only [d114, d1302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d114, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4729 p hg
    simpa only [d114, d1302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4731 (p : Pattern) (guard : d857 p = 1) : d115 p ≤ (2 : Int) + d1303 p := by
  cases selected : p 106 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d115, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4721 p hg
    simpa only [d115, d1303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d115, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4730 p hg
    simpa only [d115, d1303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4732 (p : Pattern) (guard : d857 p = 1) : d116 p ≤ (2 : Int) + d1304 p := by
  cases selected : p 86 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d116, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4686 p hg
    simpa only [d116, d1304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d116, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4731 p hg
    simpa only [d116, d1304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4733 (p : Pattern) (guard : d857 p = 1) : d117 p ≤ (2 : Int) + d1299 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d117, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4679 p hg
    simpa only [d117, d1299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d117, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4684 p hg
    simpa only [d117, d1299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4734 (p : Pattern) (guard : d857 p = 1) : d118 p ≤ (2 : Int) + d1300 p := by
  cases selected : p 106 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d118, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4665 p hg
    simpa only [d118, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d118, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4733 p hg
    simpa only [d118, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4735 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (2 : Int) + d58 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4620 p hg
    simpa only [d119, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4378 p hg
    simpa only [d119, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4736 (p : Pattern) (guard : d857 p = 1) : d120 p ≤ (2 : Int) + d58 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4735 p hg
    simpa only [d857, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4653 p hg
    simpa only [d857, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4737 (p : Pattern) (guard : d857 p = 1) : d121 p ≤ (2 : Int) + d519 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d121, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4692 p hg
    simpa only [d121, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d121, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4736 p hg
    simpa only [d121, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4738 (p : Pattern) (guard : d857 p = 1) : d122 p ≤ (2 : Int) + d520 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d122, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4737 p hg
    simpa only [d122, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d122, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4709 p hg
    simpa only [d122, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4739 (p : Pattern) (guard : d857 p = 1) : d123 p ≤ (2 : Int) + d1295 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d123, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4696 p hg
    simpa only [d123, d1295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d123, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4738 p hg
    simpa only [d123, d1295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4740 (p : Pattern) (guard : d857 p = 1) : d124 p ≤ (2 : Int) + d1296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d124, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4638 p hg
    simpa only [d124, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d124, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4739 p hg
    simpa only [d124, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4741 (p : Pattern) (guard : d857 p = 1) : d126 p ≤ (2 : Int) + d126 p := by
  omega
theorem compare4742 (p : Pattern) (guard : d857 p = 1) : d127 p ≤ (2 : Int) + d126 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4720 p hg
    simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4741 p hg
    simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4743 (p : Pattern) (guard : d857 p = 1) : d128 p ≤ (2 : Int) + d1301 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d128, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d128, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d128, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4742 p hg
    simpa only [d128, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4744 (p : Pattern) (guard : d857 p = 1) : d129 p ≤ (2 : Int) + d1298 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d129, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4679 p hg
    simpa only [d129, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d129, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4683 p hg
    simpa only [d129, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4745 (p : Pattern) (guard : d857 p = 1) : d130 p ≤ (2 : Int) + d130 p := by
  omega
theorem compare4746 (p : Pattern) (guard : d857 p = 1) : d131 p ≤ (2 : Int) + d1305 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d131, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4744 p hg
    simpa only [d131, d1305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d131, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4745 p hg
    simpa only [d131, d1305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4747 (p : Pattern) (guard : d857 p = 1) : d132 p ≤ (2 : Int) + d1306 p := by
  cases selected : p 106 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d132, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4743 p hg
    simpa only [d132, d1306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d132, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4746 p hg
    simpa only [d132, d1306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4748 (p : Pattern) (guard : d857 p = 1) : d133 p ≤ (2 : Int) + d1307 p := by
  cases selected : p 86 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d133, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4734 p hg
    simpa only [d133, d1307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d133, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4747 p hg
    simpa only [d133, d1307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4749 (p : Pattern) (guard : d857 p = 1) : d134 p ≤ (2 : Int) + d1308 p := by
  cases selected : p 80 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d134, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4732 p hg
    simpa only [d134, d1308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d134, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4748 p hg
    simpa only [d134, d1308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4750 (p : Pattern) (guard : d915 p = 1) : d16 p ≤ (2 : Int) + d16 p := by
  omega
theorem compare4751 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d3 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4307 p hg
    simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4372 p hg
    simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4752 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (2 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4753 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (2 : Int) + d18 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4306 p hg
    simpa only [d6, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4752 p hg
    simpa only [d6, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4754 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d4, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4373 p hg
    simpa only [d4, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4755 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (2 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4754 p hg
    simpa only [d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4756 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (2 : Int) + d20 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4753 p hg
    simpa only [d8, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4755 p hg
    simpa only [d8, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4757 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d9 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4316 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4358 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4758 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (2 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4757 p hg
    simpa only [d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4759 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d22 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d12, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4315 p hg
    simpa only [d12, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d12, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4758 p hg
    simpa only [d12, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
