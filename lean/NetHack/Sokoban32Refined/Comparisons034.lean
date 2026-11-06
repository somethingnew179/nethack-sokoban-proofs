/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons033
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4760 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (2 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4757 p hg
    simpa only [d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4359 p hg
    simpa only [d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4761 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (2 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4760 p hg
    simpa only [d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4762 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4759 p hg
    simpa only [d14, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4761 p hg
    simpa only [d14, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4763 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (2 : Int) + d25 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4756 p hg
    simpa only [d15, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4762 p hg
    simpa only [d15, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4764 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (2 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4756 p hg
    simpa only [d16, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4763 p hg
    simpa only [d16, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4765 (p : Pattern) (guard : d0 p = 1) : d26 p ≤ (2 : Int) + d26 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4766 (p : Pattern) (guard : d915 p = 1) : d27 p ≤ (2 : Int) + d26 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4764 p hg
    simpa only [d915, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4765 p hg
    simpa only [d915, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4767 (p : Pattern) (guard : d915 p = 1) : d28 p ≤ (2 : Int) + d1309 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d28, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4750 p hg
    simpa only [d28, d1309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d28, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4766 p hg
    simpa only [d28, d1309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4768 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4307 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4350 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4769 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (2 : Int) + d30 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4768 p hg
    simpa only [d5, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d5, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4770 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (2 : Int) + d31 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4306 p hg
    simpa only [d6, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4769 p hg
    simpa only [d6, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4771 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d30 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4768 p hg
    simpa only [d4, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4373 p hg
    simpa only [d4, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4772 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (2 : Int) + d32 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d7, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4771 p hg
    simpa only [d7, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d7, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d7, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4773 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (2 : Int) + d33 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4770 p hg
    simpa only [d8, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4772 p hg
    simpa only [d8, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4774 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (2 : Int) + d34 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4773 p hg
    simpa only [d15, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4762 p hg
    simpa only [d15, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4775 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (2 : Int) + d35 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4773 p hg
    simpa only [d16, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4774 p hg
    simpa only [d16, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4776 (p : Pattern) (guard : d0 p = 1) : d35 p ≤ (2 : Int) + d35 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4777 (p : Pattern) (guard : d915 p = 1) : d36 p ≤ (2 : Int) + d35 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4775 p hg
    simpa only [d915, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4776 p hg
    simpa only [d915, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4778 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (2 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4752 p hg
    simpa only [d37, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d37, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4779 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (2 : Int) + d20 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4753 p hg
    simpa only [d38, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4778 p hg
    simpa only [d38, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4780 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (2 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4758 p hg
    simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4781 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (2 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4759 p hg
    simpa only [d40, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4780 p hg
    simpa only [d40, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4782 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (2 : Int) + d25 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4779 p hg
    simpa only [d41, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4781 p hg
    simpa only [d41, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4783 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (2 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d42, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4779 p hg
    simpa only [d42, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d42, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4782 p hg
    simpa only [d42, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4784 (p : Pattern) (guard : d915 p = 1) : d43 p ≤ (2 : Int) + d26 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4783 p hg
    simpa only [d915, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4765 p hg
    simpa only [d915, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4785 (p : Pattern) (guard : d915 p = 1) : d44 p ≤ (2 : Int) + d1310 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d44, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4777 p hg
    simpa only [d44, d1310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d44, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4784 p hg
    simpa only [d44, d1310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4786 (p : Pattern) (guard : d915 p = 1) : d45 p ≤ (2 : Int) + d1311 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d45, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4767 p hg
    simpa only [d45, d1311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d45, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4785 p hg
    simpa only [d45, d1311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4787 (p : Pattern) (guard : d915 p = 1) : d15 p ≤ (2 : Int) + d15 p := by
  omega
theorem compare4788 (p : Pattern) (guard : d915 p = 1) : d46 p ≤ (2 : Int) + d25 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4763 p hg
    simpa only [d915, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4616 p hg
    simpa only [d915, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4789 (p : Pattern) (guard : d915 p = 1) : d47 p ≤ (2 : Int) + d1312 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d47, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4787 p hg
    simpa only [d47, d1312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d47, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4788 p hg
    simpa only [d47, d1312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4790 (p : Pattern) (guard : d915 p = 1) : d48 p ≤ (2 : Int) + d34 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4774 p hg
    simpa only [d915, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4627 p hg
    simpa only [d915, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4791 (p : Pattern) (guard : d915 p = 1) : d49 p ≤ (2 : Int) + d25 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4782 p hg
    simpa only [d915, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4616 p hg
    simpa only [d915, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4792 (p : Pattern) (guard : d915 p = 1) : d50 p ≤ (2 : Int) + d1313 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d50, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4790 p hg
    simpa only [d50, d1313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d50, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4791 p hg
    simpa only [d50, d1313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4793 (p : Pattern) (guard : d915 p = 1) : d51 p ≤ (2 : Int) + d1314 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d51, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4789 p hg
    simpa only [d51, d1314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d51, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4792 p hg
    simpa only [d51, d1314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4794 (p : Pattern) (guard : d915 p = 1) : d53 p ≤ (2 : Int) + d53 p := by
  omega
theorem compare4795 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (2 : Int) + d54 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d52, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4756 p hg
    simpa only [d52, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d52, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d52, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4796 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (2 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4763 p hg
    simpa only [d53, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4795 p hg
    simpa only [d53, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4797 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (2 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4798 (p : Pattern) (guard : d915 p = 1) : d56 p ≤ (2 : Int) + d55 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4796 p hg
    simpa only [d915, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4797 p hg
    simpa only [d915, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4799 (p : Pattern) (guard : d915 p = 1) : d57 p ≤ (2 : Int) + d1315 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d57, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4794 p hg
    simpa only [d57, d1315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d57, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4798 p hg
    simpa only [d57, d1315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4800 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (2 : Int) + d58 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d52, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4773 p hg
    simpa only [d52, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d52, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d52, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4801 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (2 : Int) + d59 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4774 p hg
    simpa only [d53, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4800 p hg
    simpa only [d53, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4802 (p : Pattern) (guard : d0 p = 1) : d59 p ≤ (2 : Int) + d59 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4803 (p : Pattern) (guard : d915 p = 1) : d60 p ≤ (2 : Int) + d59 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4801 p hg
    simpa only [d915, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4802 p hg
    simpa only [d915, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4804 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (2 : Int) + d54 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4779 p hg
    simpa only [d61, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d61, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4805 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (2 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4782 p hg
    simpa only [d62, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4804 p hg
    simpa only [d62, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4806 (p : Pattern) (guard : d915 p = 1) : d63 p ≤ (2 : Int) + d55 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4805 p hg
    simpa only [d915, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4797 p hg
    simpa only [d915, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4807 (p : Pattern) (guard : d915 p = 1) : d64 p ≤ (2 : Int) + d1316 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d64, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4803 p hg
    simpa only [d64, d1316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d64, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d64, d1316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4808 (p : Pattern) (guard : d915 p = 1) : d65 p ≤ (2 : Int) + d1317 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d65, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4799 p hg
    simpa only [d65, d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d65, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4807 p hg
    simpa only [d65, d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4809 (p : Pattern) (guard : d915 p = 1) : d66 p ≤ (2 : Int) + d1318 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d66, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4793 p hg
    simpa only [d66, d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d66, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4808 p hg
    simpa only [d66, d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4810 (p : Pattern) (guard : d915 p = 1) : d67 p ≤ (2 : Int) + d1319 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d67, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4786 p hg
    simpa only [d67, d1319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d67, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4809 p hg
    simpa only [d67, d1319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4811 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (2 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4781 p hg
    simpa only [d68, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d68, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4812 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (2 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4781 p hg
    simpa only [d69, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4811 p hg
    simpa only [d69, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4813 (p : Pattern) (guard : d0 p = 1) : d71 p ≤ (2 : Int) + d71 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4814 (p : Pattern) (guard : d915 p = 1) : d72 p ≤ (2 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4812 p hg
    simpa only [d915, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4813 p hg
    simpa only [d915, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4815 (p : Pattern) (guard : d915 p = 1) : d73 p ≤ (2 : Int) + d1320 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d73, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4766 p hg
    simpa only [d73, d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d73, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4814 p hg
    simpa only [d73, d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4816 (p : Pattern) (guard : d915 p = 1) : d74 p ≤ (2 : Int) + d1321 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d74, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4767 p hg
    simpa only [d74, d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d74, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4815 p hg
    simpa only [d74, d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4817 (p : Pattern) (guard : d915 p = 1) : d75 p ≤ (2 : Int) + d70 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4811 p hg
    simpa only [d915, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4672 p hg
    simpa only [d915, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4818 (p : Pattern) (guard : d915 p = 1) : d76 p ≤ (2 : Int) + d1322 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d76, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4766 p hg
    simpa only [d76, d1322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d76, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4817 p hg
    simpa only [d76, d1322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4819 (p : Pattern) (guard : d915 p = 1) : d77 p ≤ (2 : Int) + d1323 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d77, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4767 p hg
    simpa only [d77, d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d77, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4818 p hg
    simpa only [d77, d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4820 (p : Pattern) (guard : d915 p = 1) : d78 p ≤ (2 : Int) + d1324 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d78, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4816 p hg
    simpa only [d78, d1324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d78, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4819 p hg
    simpa only [d78, d1324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4821 (p : Pattern) (guard : d915 p = 1) : d79 p ≤ (2 : Int) + d1325 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d79, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4788 p hg
    simpa only [d79, d1325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d79, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4817 p hg
    simpa only [d79, d1325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4822 (p : Pattern) (guard : d915 p = 1) : d80 p ≤ (2 : Int) + d1326 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d80, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4789 p hg
    simpa only [d80, d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d80, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4821 p hg
    simpa only [d80, d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4823 (p : Pattern) (guard : d915 p = 1) : d81 p ≤ (2 : Int) + d1327 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d81, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4798 p hg
    simpa only [d81, d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d81, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4817 p hg
    simpa only [d81, d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4824 (p : Pattern) (guard : d915 p = 1) : d82 p ≤ (2 : Int) + d1328 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d82, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4799 p hg
    simpa only [d82, d1328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d82, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4823 p hg
    simpa only [d82, d1328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4825 (p : Pattern) (guard : d915 p = 1) : d83 p ≤ (2 : Int) + d1329 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d83, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4822 p hg
    simpa only [d83, d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d83, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4824 p hg
    simpa only [d83, d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4826 (p : Pattern) (guard : d915 p = 1) : d84 p ≤ (2 : Int) + d1330 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d84, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4820 p hg
    simpa only [d84, d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d84, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4825 p hg
    simpa only [d84, d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4827 (p : Pattern) (guard : d915 p = 1) : d85 p ≤ (2 : Int) + d1331 p := by
  cases selected : p 106 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d85, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4810 p hg
    simpa only [d85, d1331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d85, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4826 p hg
    simpa only [d85, d1331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4828 (p : Pattern) (guard : d915 p = 1) : d86 p ≤ (2 : Int) + d86 p := by
  omega
theorem compare4829 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (2 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4756 p hg
    simpa only [d86, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4795 p hg
    simpa only [d86, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4830 (p : Pattern) (guard : d0 p = 1) : d87 p ≤ (2 : Int) + d87 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4831 (p : Pattern) (guard : d915 p = 1) : d88 p ≤ (2 : Int) + d87 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4829 p hg
    simpa only [d915, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4830 p hg
    simpa only [d915, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4832 (p : Pattern) (guard : d915 p = 1) : d89 p ≤ (2 : Int) + d1332 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d89, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4828 p hg
    simpa only [d89, d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d89, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4831 p hg
    simpa only [d89, d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4833 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (2 : Int) + d90 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4773 p hg
    simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4800 p hg
    simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4834 (p : Pattern) (guard : d0 p = 1) : d90 p ≤ (2 : Int) + d90 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4835 (p : Pattern) (guard : d915 p = 1) : d91 p ≤ (2 : Int) + d90 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4833 p hg
    simpa only [d915, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4834 p hg
    simpa only [d915, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4836 (p : Pattern) (guard : d1 p = 1) : d92 p ≤ (2 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d92, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4779 p hg
    simpa only [d92, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d92, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4804 p hg
    simpa only [d92, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4837 (p : Pattern) (guard : d915 p = 1) : d93 p ≤ (2 : Int) + d87 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4836 p hg
    simpa only [d915, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4830 p hg
    simpa only [d915, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4838 (p : Pattern) (guard : d915 p = 1) : d94 p ≤ (2 : Int) + d1333 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d94, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4835 p hg
    simpa only [d94, d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d94, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4837 p hg
    simpa only [d94, d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4839 (p : Pattern) (guard : d915 p = 1) : d95 p ≤ (2 : Int) + d1334 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d95, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4832 p hg
    simpa only [d95, d1334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d95, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4838 p hg
    simpa only [d95, d1334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4840 (p : Pattern) (guard : d915 p = 1) : d96 p ≤ (2 : Int) + d1335 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d96, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4786 p hg
    simpa only [d96, d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d96, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4839 p hg
    simpa only [d96, d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4841 (p : Pattern) (guard : d915 p = 1) : d98 p ≤ (2 : Int) + d98 p := by
  omega
theorem compare4842 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (2 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4762 p hg
    simpa only [d97, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d97, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4843 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (2 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d98, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4762 p hg
    simpa only [d98, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d98, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4842 p hg
    simpa only [d98, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4844 (p : Pattern) (guard : d915 p = 1) : d99 p ≤ (2 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4843 p hg
    simpa only [d915, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4813 p hg
    simpa only [d915, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4845 (p : Pattern) (guard : d915 p = 1) : d100 p ≤ (2 : Int) + d1336 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d100, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4841 p hg
    simpa only [d100, d1336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d100, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4844 p hg
    simpa only [d100, d1336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4846 (p : Pattern) (guard : d915 p = 1) : d101 p ≤ (2 : Int) + d71 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4844 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4814 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4847 (p : Pattern) (guard : d915 p = 1) : d102 p ≤ (2 : Int) + d1337 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d102, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4845 p hg
    simpa only [d102, d1337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d102, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4846 p hg
    simpa only [d102, d1337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4848 (p : Pattern) (guard : d915 p = 1) : d103 p ≤ (2 : Int) + d1338 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d103, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4840 p hg
    simpa only [d103, d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d103, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4847 p hg
    simpa only [d103, d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4849 (p : Pattern) (guard : d915 p = 1) : d104 p ≤ (2 : Int) + d1339 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d104, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4831 p hg
    simpa only [d104, d1339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d104, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4817 p hg
    simpa only [d104, d1339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4850 (p : Pattern) (guard : d915 p = 1) : d105 p ≤ (2 : Int) + d1340 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d105, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4832 p hg
    simpa only [d105, d1340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d105, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4849 p hg
    simpa only [d105, d1340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4851 (p : Pattern) (guard : d915 p = 1) : d106 p ≤ (2 : Int) + d1341 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d106, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4819 p hg
    simpa only [d106, d1341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d106, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4850 p hg
    simpa only [d106, d1341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4852 (p : Pattern) (guard : d915 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  omega
theorem compare4853 (p : Pattern) (guard : d915 p = 1) : d107 p ≤ (2 : Int) + d1342 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d107, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4844 p hg
    simpa only [d107, d1342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d107, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4852 p hg
    simpa only [d107, d1342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4854 (p : Pattern) (guard : d915 p = 1) : d108 p ≤ (2 : Int) + d1343 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d108, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4845 p hg
    simpa only [d108, d1343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d108, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4853 p hg
    simpa only [d108, d1343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4855 (p : Pattern) (guard : d915 p = 1) : d97 p ≤ (2 : Int) + d97 p := by
  omega
theorem compare4856 (p : Pattern) (guard : d915 p = 1) : d109 p ≤ (2 : Int) + d70 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4842 p hg
    simpa only [d915, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4672 p hg
    simpa only [d915, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4857 (p : Pattern) (guard : d915 p = 1) : d110 p ≤ (2 : Int) + d1344 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d110, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4855 p hg
    simpa only [d110, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d110, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4856 p hg
    simpa only [d110, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4858 (p : Pattern) (guard : d915 p = 1) : d111 p ≤ (2 : Int) + d1345 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d111, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4856 p hg
    simpa only [d111, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d111, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4852 p hg
    simpa only [d111, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4859 (p : Pattern) (guard : d915 p = 1) : d112 p ≤ (2 : Int) + d1346 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d112, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4857 p hg
    simpa only [d112, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d112, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4858 p hg
    simpa only [d112, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4860 (p : Pattern) (guard : d915 p = 1) : d113 p ≤ (2 : Int) + d1347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d113, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4854 p hg
    simpa only [d113, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d113, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4859 p hg
    simpa only [d113, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4861 (p : Pattern) (guard : d915 p = 1) : d114 p ≤ (2 : Int) + d1348 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d114, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4851 p hg
    simpa only [d114, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d114, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4860 p hg
    simpa only [d114, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4862 (p : Pattern) (guard : d915 p = 1) : d115 p ≤ (2 : Int) + d1349 p := by
  cases selected : p 106 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d115, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4848 p hg
    simpa only [d115, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d115, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4861 p hg
    simpa only [d115, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4863 (p : Pattern) (guard : d915 p = 1) : d116 p ≤ (2 : Int) + d1350 p := by
  cases selected : p 86 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d116, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4827 p hg
    simpa only [d116, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d116, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4862 p hg
    simpa only [d116, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4864 (p : Pattern) (guard : d915 p = 1) : d117 p ≤ (2 : Int) + d1351 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d117, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4819 p hg
    simpa only [d117, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d117, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4825 p hg
    simpa only [d117, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4865 (p : Pattern) (guard : d915 p = 1) : d118 p ≤ (2 : Int) + d1352 p := by
  cases selected : p 106 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d118, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4810 p hg
    simpa only [d118, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d118, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4864 p hg
    simpa only [d118, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4866 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (2 : Int) + d119 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4773 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4756 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4867 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (2 : Int) + d120 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4866 p hg
    simpa only [d86, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4800 p hg
    simpa only [d86, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4868 (p : Pattern) (guard : d0 p = 1) : d120 p ≤ (2 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4869 (p : Pattern) (guard : d915 p = 1) : d121 p ≤ (2 : Int) + d120 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4867 p hg
    simpa only [d915, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4868 p hg
    simpa only [d915, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4870 (p : Pattern) (guard : d915 p = 1) : d122 p ≤ (2 : Int) + d1353 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d122, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4869 p hg
    simpa only [d122, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d122, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4837 p hg
    simpa only [d122, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4871 (p : Pattern) (guard : d915 p = 1) : d123 p ≤ (2 : Int) + d1354 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d123, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4832 p hg
    simpa only [d123, d1354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d123, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4870 p hg
    simpa only [d123, d1354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4872 (p : Pattern) (guard : d915 p = 1) : d124 p ≤ (2 : Int) + d1355 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d124, d1355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4786 p hg
    simpa only [d124, d1355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d124, d1355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4871 p hg
    simpa only [d124, d1355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4873 (p : Pattern) (guard : d915 p = 1) : d125 p ≤ (2 : Int) + d70 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4856 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4817 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4874 (p : Pattern) (guard : d915 p = 1) : d126 p ≤ (2 : Int) + d1356 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d126, d1356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4857 p hg
    simpa only [d126, d1356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d126, d1356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4873 p hg
    simpa only [d126, d1356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4875 (p : Pattern) (guard : d915 p = 1) : d127 p ≤ (2 : Int) + d1357 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d127, d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4847 p hg
    simpa only [d127, d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d127, d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4874 p hg
    simpa only [d127, d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4876 (p : Pattern) (guard : d915 p = 1) : d128 p ≤ (2 : Int) + d1358 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d128, d1358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4872 p hg
    simpa only [d128, d1358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d128, d1358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4875 p hg
    simpa only [d128, d1358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4877 (p : Pattern) (guard : d915 p = 1) : d129 p ≤ (2 : Int) + d1359 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d129, d1359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4819 p hg
    simpa only [d129, d1359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d129, d1359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4824 p hg
    simpa only [d129, d1359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4878 (p : Pattern) (guard : d915 p = 1) : d130 p ≤ (2 : Int) + d1360 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d130, d1360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4859 p hg
    simpa only [d130, d1360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d130, d1360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4852 p hg
    simpa only [d130, d1360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4879 (p : Pattern) (guard : d915 p = 1) : d131 p ≤ (2 : Int) + d1361 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d131, d1361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4877 p hg
    simpa only [d131, d1361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d131, d1361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4878 p hg
    simpa only [d131, d1361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4880 (p : Pattern) (guard : d915 p = 1) : d132 p ≤ (2 : Int) + d1362 p := by
  cases selected : p 106 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d132, d1362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4876 p hg
    simpa only [d132, d1362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d132, d1362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4879 p hg
    simpa only [d132, d1362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4881 (p : Pattern) (guard : d915 p = 1) : d133 p ≤ (2 : Int) + d1363 p := by
  cases selected : p 86 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d133, d1363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4865 p hg
    simpa only [d133, d1363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d133, d1363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4880 p hg
    simpa only [d133, d1363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4882 (p : Pattern) (guard : d915 p = 1) : d134 p ≤ (2 : Int) + d1364 p := by
  cases selected : p 80 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d134, d1364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4863 p hg
    simpa only [d134, d1364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d134, d1364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4881 p hg
    simpa only [d134, d1364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4883 (p : Pattern) (guard : d857 p = 1) : d15 p ≤ (0 : Int) + d399 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d857, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare853 p hg
    simpa only [d857, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4884 (p : Pattern) (guard : d857 p = 1) : d25 p ≤ (0 : Int) + d400 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare217 p hg
    simpa only [d857, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d857, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4885 (p : Pattern) (guard : d857 p = 1) : d46 p ≤ (0 : Int) + d401 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d46, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4883 p hg
    simpa only [d46, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d46, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4884 p hg
    simpa only [d46, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4886 (p : Pattern) (guard : d857 p = 1) : d47 p ≤ (0 : Int) + d402 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d47, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4883 p hg
    simpa only [d47, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d47, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4885 p hg
    simpa only [d47, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4887 (p : Pattern) (guard : d857 p = 1) : d34 p ≤ (0 : Int) + d403 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare229 p hg
    simpa only [d857, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare858 p hg
    simpa only [d857, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4888 (p : Pattern) (guard : d857 p = 1) : d48 p ≤ (0 : Int) + d404 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d48, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4883 p hg
    simpa only [d48, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d48, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4887 p hg
    simpa only [d48, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4889 (p : Pattern) (guard : d857 p = 1) : d41 p ≤ (0 : Int) + d405 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare236 p hg
    simpa only [d857, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1443 p hg
    simpa only [d857, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4890 (p : Pattern) (guard : d857 p = 1) : d49 p ≤ (0 : Int) + d406 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d49, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4889 p hg
    simpa only [d49, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d49, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4884 p hg
    simpa only [d49, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4891 (p : Pattern) (guard : d857 p = 1) : d50 p ≤ (0 : Int) + d407 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d50, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4888 p hg
    simpa only [d50, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d50, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4890 p hg
    simpa only [d50, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4892 (p : Pattern) (guard : d857 p = 1) : d51 p ≤ (0 : Int) + d408 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d51, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4886 p hg
    simpa only [d51, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d51, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4891 p hg
    simpa only [d51, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4893 (p : Pattern) (guard : d0 p = 1) : d52 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4894 (p : Pattern) (guard : d857 p = 1) : d53 p ≤ (0 : Int) + d399 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d53, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d857, d53, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d53, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d857, d53, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4895 (p : Pattern) (guard : d0 p = 1) : d54 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4896 (p : Pattern) (guard : d857 p = 1) : d55 p ≤ (0 : Int) + d400 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d55, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare217 p hg
    simpa only [d857, d55, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d55, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d857, d55, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4897 (p : Pattern) (guard : d857 p = 1) : d56 p ≤ (0 : Int) + d401 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d56, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4894 p hg
    simpa only [d56, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d56, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4896 p hg
    simpa only [d56, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4898 (p : Pattern) (guard : d857 p = 1) : d57 p ≤ (0 : Int) + d402 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d57, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4894 p hg
    simpa only [d57, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d57, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4897 p hg
    simpa only [d57, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4899 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban32Refined
