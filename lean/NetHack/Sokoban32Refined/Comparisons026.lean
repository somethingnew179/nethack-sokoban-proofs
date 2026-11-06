/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3640 (p : Pattern) (guard : d1247 p = 1) : d325 p ≤ (0 : Int) + d650 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d325, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3635 p hg
    simpa only [d325, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d325, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3639 p hg
    simpa only [d325, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3641 (p : Pattern) (guard : d1247 p = 1) : d326 p ≤ (0 : Int) + d651 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d326, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3624 p hg
    simpa only [d326, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d326, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3640 p hg
    simpa only [d326, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3642 (p : Pattern) (guard : d1247 p = 1) : d327 p ≤ (0 : Int) + d652 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d327, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3610 p hg
    simpa only [d327, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d327, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3641 p hg
    simpa only [d327, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3643 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3644 (p : Pattern) (guard : d915 p = 1) : d328 p ≤ (0 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d915, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3643 p hg
    simpa only [d915, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3645 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d26 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3646 (p : Pattern) (guard : d915 p = 1) : d328 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d328, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d915, d328, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d328, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3645 p hg
    simpa only [d915, d328, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3647 (p : Pattern) (guard : d915 p = 1) : d328 p ≤ (0 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3644 p hg
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3646 p hg
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3648 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d35 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3649 (p : Pattern) (guard : d915 p = 1) : d328 p ≤ (0 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d328, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d915, d328, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d328, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3648 p hg
    simpa only [d915, d328, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3650 (p : Pattern) (guard : d915 p = 1) : d329 p ≤ (0 : Int) + d43 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d329, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare849 p hg
    simpa only [d915, d329, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d329, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3645 p hg
    simpa only [d915, d329, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3651 (p : Pattern) (guard : d915 p = 1) : d330 p ≤ (0 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d330, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3649 p hg
    simpa only [d330, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d330, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3650 p hg
    simpa only [d330, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3652 (p : Pattern) (guard : d915 p = 1) : d331 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d331, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d331, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d331, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3651 p hg
    simpa only [d331, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3653 (p : Pattern) (guard : d915 p = 1) : d332 p ≤ (0 : Int) + d15 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d915, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3066 p hg
    simpa only [d915, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3654 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d25 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3655 (p : Pattern) (guard : d915 p = 1) : d332 p ≤ (0 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d332, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d915, d332, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d332, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3654 p hg
    simpa only [d915, d332, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3656 (p : Pattern) (guard : d915 p = 1) : d332 p ≤ (0 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3653 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3655 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3657 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d34 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3658 (p : Pattern) (guard : d915 p = 1) : d332 p ≤ (0 : Int) + d48 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d332, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d915, d332, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d332, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3657 p hg
    simpa only [d915, d332, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3659 (p : Pattern) (guard : d915 p = 1) : d333 p ≤ (0 : Int) + d49 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d333, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare236 p hg
    simpa only [d915, d333, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d333, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3654 p hg
    simpa only [d915, d333, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3660 (p : Pattern) (guard : d915 p = 1) : d334 p ≤ (0 : Int) + d50 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d334, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3658 p hg
    simpa only [d334, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d334, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3659 p hg
    simpa only [d334, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3661 (p : Pattern) (guard : d915 p = 1) : d335 p ≤ (0 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d335, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3656 p hg
    simpa only [d335, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d335, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3660 p hg
    simpa only [d335, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3662 (p : Pattern) (guard : d915 p = 1) : d336 p ≤ (0 : Int) + d53 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare796 p hg
    simpa only [d915, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2735 p hg
    simpa only [d915, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3663 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3664 (p : Pattern) (guard : d915 p = 1) : d336 p ≤ (0 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d336, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare796 p hg
    simpa only [d915, d336, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d336, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3663 p hg
    simpa only [d915, d336, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3665 (p : Pattern) (guard : d915 p = 1) : d336 p ≤ (0 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3662 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3664 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3666 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d59 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3667 (p : Pattern) (guard : d915 p = 1) : d336 p ≤ (0 : Int) + d60 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d336, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare796 p hg
    simpa only [d915, d336, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d336, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3666 p hg
    simpa only [d915, d336, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3668 (p : Pattern) (guard : d915 p = 1) : d337 p ≤ (0 : Int) + d63 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d337, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare870 p hg
    simpa only [d915, d337, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d337, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3663 p hg
    simpa only [d915, d337, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3669 (p : Pattern) (guard : d915 p = 1) : d338 p ≤ (0 : Int) + d64 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d338, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3667 p hg
    simpa only [d338, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d338, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3668 p hg
    simpa only [d338, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3670 (p : Pattern) (guard : d915 p = 1) : d339 p ≤ (0 : Int) + d65 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d339, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3665 p hg
    simpa only [d339, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d339, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3669 p hg
    simpa only [d339, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3671 (p : Pattern) (guard : d915 p = 1) : d340 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d340, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3661 p hg
    simpa only [d340, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d340, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3670 p hg
    simpa only [d340, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3672 (p : Pattern) (guard : d915 p = 1) : d341 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d341, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3652 p hg
    simpa only [d341, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d341, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3671 p hg
    simpa only [d341, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3673 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d71 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3674 (p : Pattern) (guard : d915 p = 1) : d342 p ≤ (0 : Int) + d72 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d342, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare876 p hg
    simpa only [d915, d342, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d342, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3673 p hg
    simpa only [d915, d342, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3675 (p : Pattern) (guard : d915 p = 1) : d343 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d343, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3646 p hg
    simpa only [d343, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d343, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3674 p hg
    simpa only [d343, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3676 (p : Pattern) (guard : d915 p = 1) : d344 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d344, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d344, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d344, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3675 p hg
    simpa only [d344, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3677 (p : Pattern) (guard : d915 p = 1) : d345 p ≤ (0 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d345, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare881 p hg
    simpa only [d915, d345, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d345, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1685 p hg
    simpa only [d915, d345, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3678 (p : Pattern) (guard : d915 p = 1) : d346 p ≤ (0 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d346, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3646 p hg
    simpa only [d346, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d346, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3677 p hg
    simpa only [d346, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3679 (p : Pattern) (guard : d915 p = 1) : d347 p ≤ (0 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d347, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d347, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d347, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3678 p hg
    simpa only [d347, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3680 (p : Pattern) (guard : d915 p = 1) : d348 p ≤ (0 : Int) + d78 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d348, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3676 p hg
    simpa only [d348, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d348, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3679 p hg
    simpa only [d348, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3681 (p : Pattern) (guard : d915 p = 1) : d349 p ≤ (0 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d349, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3655 p hg
    simpa only [d349, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d349, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3677 p hg
    simpa only [d349, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3682 (p : Pattern) (guard : d915 p = 1) : d350 p ≤ (0 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d350, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3656 p hg
    simpa only [d350, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d350, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3681 p hg
    simpa only [d350, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3683 (p : Pattern) (guard : d915 p = 1) : d351 p ≤ (0 : Int) + d81 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d351, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3664 p hg
    simpa only [d351, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d351, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3677 p hg
    simpa only [d351, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3684 (p : Pattern) (guard : d915 p = 1) : d352 p ≤ (0 : Int) + d82 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d352, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3665 p hg
    simpa only [d352, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d352, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3683 p hg
    simpa only [d352, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3685 (p : Pattern) (guard : d915 p = 1) : d353 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d353, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3682 p hg
    simpa only [d353, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d353, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3684 p hg
    simpa only [d353, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3686 (p : Pattern) (guard : d915 p = 1) : d354 p ≤ (0 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d354, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3680 p hg
    simpa only [d354, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d354, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3685 p hg
    simpa only [d354, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3687 (p : Pattern) (guard : d915 p = 1) : d355 p ≤ (0 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d355, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3672 p hg
    simpa only [d355, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d355, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3686 p hg
    simpa only [d355, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3688 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3689 (p : Pattern) (guard : d915 p = 1) : d356 p ≤ (0 : Int) + d86 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d915, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3688 p hg
    simpa only [d915, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3690 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d87 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3691 (p : Pattern) (guard : d915 p = 1) : d356 p ≤ (0 : Int) + d88 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d356, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d915, d356, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d356, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3690 p hg
    simpa only [d915, d356, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3692 (p : Pattern) (guard : d915 p = 1) : d356 p ≤ (0 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3689 p hg
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3691 p hg
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3693 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d90 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3694 (p : Pattern) (guard : d915 p = 1) : d356 p ≤ (0 : Int) + d91 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d356, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d915, d356, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d356, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3693 p hg
    simpa only [d915, d356, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3695 (p : Pattern) (guard : d915 p = 1) : d357 p ≤ (0 : Int) + d93 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d357, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d915, d357, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d357, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3690 p hg
    simpa only [d915, d357, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3696 (p : Pattern) (guard : d915 p = 1) : d358 p ≤ (0 : Int) + d94 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d358, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3694 p hg
    simpa only [d358, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d358, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3695 p hg
    simpa only [d358, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3697 (p : Pattern) (guard : d915 p = 1) : d359 p ≤ (0 : Int) + d95 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d359, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3692 p hg
    simpa only [d359, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d359, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3696 p hg
    simpa only [d359, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3698 (p : Pattern) (guard : d915 p = 1) : d360 p ≤ (0 : Int) + d96 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d360, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3652 p hg
    simpa only [d360, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d360, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3697 p hg
    simpa only [d360, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3699 (p : Pattern) (guard : d915 p = 1) : d361 p ≤ (0 : Int) + d98 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare811 p hg
    simpa only [d915, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3100 p hg
    simpa only [d915, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3700 (p : Pattern) (guard : d915 p = 1) : d361 p ≤ (0 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d361, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare811 p hg
    simpa only [d915, d361, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d361, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3673 p hg
    simpa only [d915, d361, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3701 (p : Pattern) (guard : d915 p = 1) : d361 p ≤ (0 : Int) + d100 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3699 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3700 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3702 (p : Pattern) (guard : d915 p = 1) : d362 p ≤ (0 : Int) + d101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d362, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3700 p hg
    simpa only [d362, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d362, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3674 p hg
    simpa only [d362, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3703 (p : Pattern) (guard : d915 p = 1) : d363 p ≤ (0 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d363, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3701 p hg
    simpa only [d363, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d363, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3702 p hg
    simpa only [d363, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3704 (p : Pattern) (guard : d915 p = 1) : d364 p ≤ (0 : Int) + d103 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d364, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3698 p hg
    simpa only [d364, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d364, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d364, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3705 (p : Pattern) (guard : d915 p = 1) : d365 p ≤ (0 : Int) + d104 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d365, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3691 p hg
    simpa only [d365, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d365, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3677 p hg
    simpa only [d365, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3706 (p : Pattern) (guard : d915 p = 1) : d366 p ≤ (0 : Int) + d105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d366, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3692 p hg
    simpa only [d366, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d366, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3705 p hg
    simpa only [d366, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3707 (p : Pattern) (guard : d915 p = 1) : d367 p ≤ (0 : Int) + d106 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d367, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3679 p hg
    simpa only [d367, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d367, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3706 p hg
    simpa only [d367, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3708 (p : Pattern) (guard : d915 p = 1) : d368 p ≤ (0 : Int) + d107 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d368, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3700 p hg
    simpa only [d368, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d368, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare916 p hg
    simpa only [d368, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3709 (p : Pattern) (guard : d915 p = 1) : d369 p ≤ (0 : Int) + d108 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d369, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3701 p hg
    simpa only [d369, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d369, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3708 p hg
    simpa only [d369, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3710 (p : Pattern) (guard : d915 p = 1) : d370 p ≤ (0 : Int) + d97 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare831 p hg
    simpa only [d915, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2724 p hg
    simpa only [d915, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3711 (p : Pattern) (guard : d915 p = 1) : d370 p ≤ (0 : Int) + d109 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d370, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare831 p hg
    simpa only [d915, d370, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d370, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1685 p hg
    simpa only [d915, d370, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3712 (p : Pattern) (guard : d915 p = 1) : d370 p ≤ (0 : Int) + d110 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3710 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3711 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3713 (p : Pattern) (guard : d915 p = 1) : d371 p ≤ (0 : Int) + d111 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d371, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3711 p hg
    simpa only [d371, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d371, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare916 p hg
    simpa only [d371, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3714 (p : Pattern) (guard : d915 p = 1) : d372 p ≤ (0 : Int) + d112 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d372, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3712 p hg
    simpa only [d372, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d372, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3713 p hg
    simpa only [d372, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3715 (p : Pattern) (guard : d915 p = 1) : d373 p ≤ (0 : Int) + d113 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d373, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3709 p hg
    simpa only [d373, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d373, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3714 p hg
    simpa only [d373, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3716 (p : Pattern) (guard : d915 p = 1) : d374 p ≤ (0 : Int) + d114 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d374, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3707 p hg
    simpa only [d374, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d374, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3715 p hg
    simpa only [d374, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3717 (p : Pattern) (guard : d915 p = 1) : d375 p ≤ (0 : Int) + d115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d375, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3704 p hg
    simpa only [d375, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d375, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3716 p hg
    simpa only [d375, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3718 (p : Pattern) (guard : d915 p = 1) : d376 p ≤ (0 : Int) + d116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d376, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3687 p hg
    simpa only [d376, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d376, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3717 p hg
    simpa only [d376, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3719 (p : Pattern) (guard : d915 p = 1) : d377 p ≤ (0 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d377, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3679 p hg
    simpa only [d377, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d377, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3685 p hg
    simpa only [d377, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3720 (p : Pattern) (guard : d915 p = 1) : d378 p ≤ (0 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d378, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3672 p hg
    simpa only [d378, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d378, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3719 p hg
    simpa only [d378, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3721 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3722 (p : Pattern) (guard : d915 p = 1) : d356 p ≤ (0 : Int) + d121 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d356, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d915, d356, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d356, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3721 p hg
    simpa only [d915, d356, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3723 (p : Pattern) (guard : d915 p = 1) : d358 p ≤ (0 : Int) + d122 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d358, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3722 p hg
    simpa only [d358, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d358, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3695 p hg
    simpa only [d358, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3724 (p : Pattern) (guard : d915 p = 1) : d359 p ≤ (0 : Int) + d123 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d359, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3692 p hg
    simpa only [d359, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d359, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3723 p hg
    simpa only [d359, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3725 (p : Pattern) (guard : d915 p = 1) : d360 p ≤ (0 : Int) + d124 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d360, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3652 p hg
    simpa only [d360, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d360, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3724 p hg
    simpa only [d360, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3726 (p : Pattern) (guard : d915 p = 1) : d379 p ≤ (0 : Int) + d125 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d379, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3711 p hg
    simpa only [d379, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d379, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3677 p hg
    simpa only [d379, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3727 (p : Pattern) (guard : d915 p = 1) : d380 p ≤ (0 : Int) + d126 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d380, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3712 p hg
    simpa only [d380, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d380, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3726 p hg
    simpa only [d380, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3728 (p : Pattern) (guard : d915 p = 1) : d381 p ≤ (0 : Int) + d127 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d381, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d381, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d381, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3727 p hg
    simpa only [d381, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3729 (p : Pattern) (guard : d915 p = 1) : d382 p ≤ (0 : Int) + d128 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d382, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3725 p hg
    simpa only [d382, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d382, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3728 p hg
    simpa only [d382, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3730 (p : Pattern) (guard : d915 p = 1) : d383 p ≤ (0 : Int) + d129 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d383, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3679 p hg
    simpa only [d383, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d383, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3684 p hg
    simpa only [d383, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3731 (p : Pattern) (guard : d915 p = 1) : d384 p ≤ (0 : Int) + d130 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d384, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3714 p hg
    simpa only [d384, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d384, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare916 p hg
    simpa only [d384, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3732 (p : Pattern) (guard : d915 p = 1) : d385 p ≤ (0 : Int) + d131 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d385, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3730 p hg
    simpa only [d385, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d385, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3731 p hg
    simpa only [d385, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3733 (p : Pattern) (guard : d915 p = 1) : d386 p ≤ (0 : Int) + d132 p := by
  cases selected : p 106 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d386, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3729 p hg
    simpa only [d386, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d386, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3732 p hg
    simpa only [d386, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3734 (p : Pattern) (guard : d915 p = 1) : d387 p ≤ (0 : Int) + d133 p := by
  cases selected : p 86 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d387, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3720 p hg
    simpa only [d387, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d387, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3733 p hg
    simpa only [d387, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3735 (p : Pattern) (guard : d915 p = 1) : d388 p ≤ (0 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d388, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3718 p hg
    simpa only [d388, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d388, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3734 p hg
    simpa only [d388, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3736 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3737 (p : Pattern) (guard : d1248 p = 1) : d328 p ≤ (0 : Int) + d700 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3417 p hg
    simpa only [d1248, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3736 p hg
    simpa only [d1248, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3738 (p : Pattern) (guard : d917 p = 1) : d37 p ≤ (0 : Int) + d37 p := by
  omega
theorem compare3739 (p : Pattern) (guard : d917 p = 1) : d38 p ≤ (0 : Int) + d697 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d38, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3407 p hg
    simpa only [d38, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d38, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3738 p hg
    simpa only [d38, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3740 (p : Pattern) (guard : d917 p = 1) : d39 p ≤ (0 : Int) + d39 p := by
  omega
theorem compare3741 (p : Pattern) (guard : d917 p = 1) : d40 p ≤ (0 : Int) + d698 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d40, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3413 p hg
    simpa only [d40, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d40, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3740 p hg
    simpa only [d40, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3742 (p : Pattern) (guard : d917 p = 1) : d41 p ≤ (0 : Int) + d699 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d41, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3739 p hg
    simpa only [d41, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d41, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3741 p hg
    simpa only [d41, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3743 (p : Pattern) (guard : d917 p = 1) : d42 p ≤ (0 : Int) + d700 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d42, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3739 p hg
    simpa only [d42, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d42, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3742 p hg
    simpa only [d42, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3744 (p : Pattern) (guard : d1248 p = 1) : d329 p ≤ (0 : Int) + d700 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3743 p hg
    simpa only [d1248, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3736 p hg
    simpa only [d1248, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3745 (p : Pattern) (guard : d1248 p = 1) : d330 p ≤ (0 : Int) + d700 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3737 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3744 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3746 (p : Pattern) (guard : d1248 p = 1) : d331 p ≤ (0 : Int) + d700 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3737 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3745 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3747 (p : Pattern) (guard : d1248 p = 1) : d332 p ≤ (0 : Int) + d699 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3416 p hg
    simpa only [d1248, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3432 p hg
    simpa only [d1248, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3748 (p : Pattern) (guard : d1248 p = 1) : d333 p ≤ (0 : Int) + d699 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3742 p hg
    simpa only [d1248, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3432 p hg
    simpa only [d1248, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3749 (p : Pattern) (guard : d1248 p = 1) : d334 p ≤ (0 : Int) + d699 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3747 p hg
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3748 p hg
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3750 (p : Pattern) (guard : d1248 p = 1) : d335 p ≤ (0 : Int) + d699 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3747 p hg
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3749 p hg
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3751 (p : Pattern) (guard : d1248 p = 1) : d336 p ≤ (0 : Int) + d702 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3435 p hg
    simpa only [d1248, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3440 p hg
    simpa only [d1248, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3752 (p : Pattern) (guard : d917 p = 1) : d61 p ≤ (0 : Int) + d701 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d61, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3739 p hg
    simpa only [d61, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d61, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d61, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3753 (p : Pattern) (guard : d917 p = 1) : d62 p ≤ (0 : Int) + d702 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d62, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3742 p hg
    simpa only [d62, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d62, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3752 p hg
    simpa only [d62, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3754 (p : Pattern) (guard : d1248 p = 1) : d337 p ≤ (0 : Int) + d702 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3753 p hg
    simpa only [d1248, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3440 p hg
    simpa only [d1248, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3755 (p : Pattern) (guard : d1248 p = 1) : d338 p ≤ (0 : Int) + d702 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3751 p hg
    simpa only [d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3756 (p : Pattern) (guard : d1248 p = 1) : d339 p ≤ (0 : Int) + d702 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3751 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3755 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3757 (p : Pattern) (guard : d1248 p = 1) : d340 p ≤ (0 : Int) + d703 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d340, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3750 p hg
    simpa only [d340, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d340, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3756 p hg
    simpa only [d340, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3758 (p : Pattern) (guard : d1248 p = 1) : d341 p ≤ (0 : Int) + d704 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d341, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3746 p hg
    simpa only [d341, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d341, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d341, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3759 (p : Pattern) (guard : d917 p = 1) : d68 p ≤ (0 : Int) + d705 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d68, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3741 p hg
    simpa only [d68, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d68, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d68, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3760 (p : Pattern) (guard : d917 p = 1) : d69 p ≤ (0 : Int) + d706 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d69, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3741 p hg
    simpa only [d69, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d69, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3759 p hg
    simpa only [d69, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3761 (p : Pattern) (guard : d1248 p = 1) : d342 p ≤ (0 : Int) + d706 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3760 p hg
    simpa only [d1248, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3473 p hg
    simpa only [d1248, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3762 (p : Pattern) (guard : d1248 p = 1) : d343 p ≤ (0 : Int) + d707 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d343, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3737 p hg
    simpa only [d343, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d343, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3761 p hg
    simpa only [d343, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3763 (p : Pattern) (guard : d1248 p = 1) : d344 p ≤ (0 : Int) + d708 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d344, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3737 p hg
    simpa only [d344, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d344, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3762 p hg
    simpa only [d344, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3764 (p : Pattern) (guard : d1248 p = 1) : d345 p ≤ (0 : Int) + d705 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3759 p hg
    simpa only [d1248, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3451 p hg
    simpa only [d1248, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3765 (p : Pattern) (guard : d1248 p = 1) : d346 p ≤ (0 : Int) + d709 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d346, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3737 p hg
    simpa only [d346, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d346, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3764 p hg
    simpa only [d346, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3766 (p : Pattern) (guard : d1248 p = 1) : d347 p ≤ (0 : Int) + d710 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d347, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3737 p hg
    simpa only [d347, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d347, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3765 p hg
    simpa only [d347, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3767 (p : Pattern) (guard : d1248 p = 1) : d348 p ≤ (0 : Int) + d711 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d348, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3763 p hg
    simpa only [d348, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d348, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3766 p hg
    simpa only [d348, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3768 (p : Pattern) (guard : d1248 p = 1) : d349 p ≤ (0 : Int) + d712 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d349, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3747 p hg
    simpa only [d349, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d349, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3764 p hg
    simpa only [d349, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3769 (p : Pattern) (guard : d1248 p = 1) : d350 p ≤ (0 : Int) + d713 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d350, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3747 p hg
    simpa only [d350, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d350, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3768 p hg
    simpa only [d350, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3770 (p : Pattern) (guard : d1248 p = 1) : d351 p ≤ (0 : Int) + d714 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d351, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3751 p hg
    simpa only [d351, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d351, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3764 p hg
    simpa only [d351, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3771 (p : Pattern) (guard : d1248 p = 1) : d352 p ≤ (0 : Int) + d715 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d352, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3751 p hg
    simpa only [d352, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d352, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3770 p hg
    simpa only [d352, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3772 (p : Pattern) (guard : d1248 p = 1) : d353 p ≤ (0 : Int) + d716 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d353, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3769 p hg
    simpa only [d353, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d353, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3771 p hg
    simpa only [d353, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3773 (p : Pattern) (guard : d1248 p = 1) : d354 p ≤ (0 : Int) + d717 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d354, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3767 p hg
    simpa only [d354, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d354, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3772 p hg
    simpa only [d354, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3774 (p : Pattern) (guard : d1248 p = 1) : d355 p ≤ (0 : Int) + d718 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d355, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3758 p hg
    simpa only [d355, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d355, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3773 p hg
    simpa only [d355, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3775 (p : Pattern) (guard : d1248 p = 1) : d356 p ≤ (0 : Int) + d719 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3459 p hg
    simpa only [d1248, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3499 p hg
    simpa only [d1248, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3776 (p : Pattern) (guard : d917 p = 1) : d92 p ≤ (0 : Int) + d719 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d92, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3739 p hg
    simpa only [d92, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d92, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3752 p hg
    simpa only [d92, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3777 (p : Pattern) (guard : d1248 p = 1) : d357 p ≤ (0 : Int) + d719 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3776 p hg
    simpa only [d1248, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3499 p hg
    simpa only [d1248, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3778 (p : Pattern) (guard : d1248 p = 1) : d358 p ≤ (0 : Int) + d719 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3775 p hg
    simpa only [d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3777 p hg
    simpa only [d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3779 (p : Pattern) (guard : d1248 p = 1) : d359 p ≤ (0 : Int) + d719 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3775 p hg
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3778 p hg
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
