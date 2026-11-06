/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons026
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3780 (p : Pattern) (guard : d1016 p = 1) : d63 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d63, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2400 p hg
    simpa only [d1016, d63, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d63, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare686 p hg
    simpa only [d1016, d63, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3781 (p : Pattern) (guard : d1050 p = 1) : d63 p ≤ (0 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare687 p hg
    simpa only [d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3780 p hg
    simpa only [d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3782 (p : Pattern) (guard : d1050 p = 1) : d64 p ≤ (0 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d64, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3779 p hg
    simpa only [d64, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d64, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3781 p hg
    simpa only [d64, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3783 (p : Pattern) (guard : d0 p = 1) : d119 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3784 (p : Pattern) (guard : d829 p = 1) : d120 p ≤ (0 : Int) + d7 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d829, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3783 p hg
    simpa only [d829, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3785 (p : Pattern) (guard : d1016 p = 1) : d121 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3784 p hg
    simpa only [d1016, d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d1016, d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3786 (p : Pattern) (guard : d1050 p = 1) : d122 p ≤ (0 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d1050, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare690 p hg
    simpa only [d1050, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d1050, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3785 p hg
    simpa only [d1050, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3787 (p : Pattern) (guard : d1050 p = 1) : d179 p ≤ (0 : Int) + d106 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2404 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3786 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3788 (p : Pattern) (guard : d0 p = 1) : d125 p ≤ (0 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3789 (p : Pattern) (guard : d829 p = 1) : d126 p ≤ (0 : Int) + d11 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare295 p hg
    simpa only [d829, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3788 p hg
    simpa only [d829, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3790 (p : Pattern) (guard : d829 p = 1) : d127 p ≤ (0 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3784 p hg
    simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3789 p hg
    simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3791 (p : Pattern) (guard : d1016 p = 1) : d128 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3790 p hg
    simpa only [d1016, d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d1016, d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3792 (p : Pattern) (guard : d1050 p = 1) : d129 p ≤ (0 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d1050, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare695 p hg
    simpa only [d1050, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d1050, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3791 p hg
    simpa only [d1050, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3793 (p : Pattern) (guard : d1050 p = 1) : d237 p ≤ (0 : Int) + d109 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2410 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3792 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3794 (p : Pattern) (guard : d1050 p = 1) : d238 p ≤ (0 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d238, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3787 p hg
    simpa only [d238, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d238, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3793 p hg
    simpa only [d238, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3795 (p : Pattern) (guard : d1050 p = 1) : d239 p ≤ (0 : Int) + d227 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3782 p hg
    simpa only [d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3794 p hg
    simpa only [d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3796 (p : Pattern) (guard : d1050 p = 1) : d68 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d68, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3779 p hg
    simpa only [d68, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d68, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2419 p hg
    simpa only [d68, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3797 (p : Pattern) (guard : d1050 p = 1) : d69 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d69, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3781 p hg
    simpa only [d69, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d69, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2421 p hg
    simpa only [d69, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3798 (p : Pattern) (guard : d1050 p = 1) : d70 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d70, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3796 p hg
    simpa only [d70, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d70, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3797 p hg
    simpa only [d70, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3799 (p : Pattern) (guard : d1050 p = 1) : d181 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d181, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3786 p hg
    simpa only [d181, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d181, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2419 p hg
    simpa only [d181, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3800 (p : Pattern) (guard : d1050 p = 1) : d240 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d240, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3792 p hg
    simpa only [d240, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d240, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2421 p hg
    simpa only [d240, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3801 (p : Pattern) (guard : d1050 p = 1) : d241 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d241, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3799 p hg
    simpa only [d241, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d241, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3800 p hg
    simpa only [d241, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3802 (p : Pattern) (guard : d1050 p = 1) : d242 p ≤ (0 : Int) + d231 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3798 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3801 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3803 (p : Pattern) (guard : d1050 p = 1) : d243 p ≤ (0 : Int) + d366 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d243, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3795 p hg
    simpa only [d243, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d243, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3802 p hg
    simpa only [d243, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3804 (p : Pattern) (guard : d1050 p = 1) : d244 p ≤ (0 : Int) + d367 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d244, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3802 p hg
    simpa only [d244, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d244, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2429 p hg
    simpa only [d244, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3805 (p : Pattern) (guard : d1050 p = 1) : d245 p ≤ (0 : Int) + d368 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d245, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3803 p hg
    simpa only [d245, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d245, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3804 p hg
    simpa only [d245, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3806 (p : Pattern) (guard : d1016 p = 1) : d139 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d139, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3784 p hg
    simpa only [d1016, d139, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d139, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1866 p hg
    simpa only [d1016, d139, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3807 (p : Pattern) (guard : d1050 p = 1) : d153 p ≤ (0 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d1050, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare685 p hg
    simpa only [d1050, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d1050, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3806 p hg
    simpa only [d1050, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3808 (p : Pattern) (guard : d1050 p = 1) : d186 p ≤ (0 : Int) + d106 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3779 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3807 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3809 (p : Pattern) (guard : d1016 p = 1) : d146 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d146, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3790 p hg
    simpa only [d1016, d146, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d146, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1870 p hg
    simpa only [d1016, d146, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3810 (p : Pattern) (guard : d1050 p = 1) : d155 p ≤ (0 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d1050, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare687 p hg
    simpa only [d1050, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d1050, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3809 p hg
    simpa only [d1050, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3811 (p : Pattern) (guard : d1050 p = 1) : d246 p ≤ (0 : Int) + d109 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3781 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3810 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3812 (p : Pattern) (guard : d1050 p = 1) : d247 p ≤ (0 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d247, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3808 p hg
    simpa only [d247, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d247, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3811 p hg
    simpa only [d247, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3813 (p : Pattern) (guard : d1050 p = 1) : d248 p ≤ (0 : Int) + d369 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d248, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3812 p hg
    simpa only [d248, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d248, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2429 p hg
    simpa only [d248, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3814 (p : Pattern) (guard : d1050 p = 1) : d140 p ≤ (0 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d1050, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1867 p hg
    simpa only [d1050, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d1050, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3806 p hg
    simpa only [d1050, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3815 (p : Pattern) (guard : d1050 p = 1) : d188 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d188, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3814 p hg
    simpa only [d188, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d188, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2419 p hg
    simpa only [d188, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3816 (p : Pattern) (guard : d1050 p = 1) : d147 p ≤ (0 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d1050, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1871 p hg
    simpa only [d1050, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d1050, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3809 p hg
    simpa only [d1050, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3817 (p : Pattern) (guard : d1050 p = 1) : d249 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d249, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3816 p hg
    simpa only [d249, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d249, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2421 p hg
    simpa only [d249, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3818 (p : Pattern) (guard : d1050 p = 1) : d250 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d250, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3815 p hg
    simpa only [d250, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d250, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3817 p hg
    simpa only [d250, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3819 (p : Pattern) (guard : d1050 p = 1) : d251 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d251, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3818 p hg
    simpa only [d251, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d251, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2429 p hg
    simpa only [d251, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3820 (p : Pattern) (guard : d1050 p = 1) : d252 p ≤ (0 : Int) + d371 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d252, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3813 p hg
    simpa only [d252, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d252, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3819 p hg
    simpa only [d252, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3821 (p : Pattern) (guard : d1050 p = 1) : d191 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d191, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3807 p hg
    simpa only [d191, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d191, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2419 p hg
    simpa only [d191, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3822 (p : Pattern) (guard : d1050 p = 1) : d253 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d253, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3810 p hg
    simpa only [d253, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d253, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2421 p hg
    simpa only [d253, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3823 (p : Pattern) (guard : d1050 p = 1) : d254 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d254, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3821 p hg
    simpa only [d254, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d254, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3822 p hg
    simpa only [d254, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3824 (p : Pattern) (guard : d1050 p = 1) : d255 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d255, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3823 p hg
    simpa only [d255, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d255, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2429 p hg
    simpa only [d255, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3825 (p : Pattern) (guard : d1050 p = 1) : d256 p ≤ (0 : Int) + d372 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d256, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3824 p hg
    simpa only [d256, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d256, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2429 p hg
    simpa only [d256, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3826 (p : Pattern) (guard : d1050 p = 1) : d257 p ≤ (0 : Int) + d373 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d257, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3820 p hg
    simpa only [d257, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d257, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3825 p hg
    simpa only [d257, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3827 (p : Pattern) (guard : d1050 p = 1) : d258 p ≤ (0 : Int) + d374 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d258, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3805 p hg
    simpa only [d258, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d258, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3826 p hg
    simpa only [d258, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3828 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3829 (p : Pattern) (guard : d829 p = 1) : d56 p ≤ (0 : Int) + d7 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d829, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3828 p hg
    simpa only [d829, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3830 (p : Pattern) (guard : d1016 p = 1) : d56 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3829 p hg
    simpa only [d1016, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare684 p hg
    simpa only [d1016, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3831 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (0 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3832 (p : Pattern) (guard : d829 p = 1) : d61 p ≤ (0 : Int) + d11 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare295 p hg
    simpa only [d829, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3831 p hg
    simpa only [d829, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3833 (p : Pattern) (guard : d829 p = 1) : d62 p ≤ (0 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3829 p hg
    simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3832 p hg
    simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3834 (p : Pattern) (guard : d1016 p = 1) : d62 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3833 p hg
    simpa only [d1016, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare686 p hg
    simpa only [d1016, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3835 (p : Pattern) (guard : d1016 p = 1) : d451 p ≤ (0 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d451, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3830 p hg
    simpa only [d451, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d451, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3834 p hg
    simpa only [d451, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3836 (p : Pattern) (guard : d1016 p = 1) : d452 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d452, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3829 p hg
    simpa only [d1016, d452, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d452, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d1016, d452, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3837 (p : Pattern) (guard : d1016 p = 1) : d453 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d453, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3833 p hg
    simpa only [d1016, d453, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d453, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d1016, d453, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3838 (p : Pattern) (guard : d1016 p = 1) : d454 p ≤ (0 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d454, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3836 p hg
    simpa only [d454, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d454, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3837 p hg
    simpa only [d454, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3839 (p : Pattern) (guard : d1016 p = 1) : d455 p ≤ (0 : Int) + d227 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3835 p hg
    simpa only [d455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3838 p hg
    simpa only [d455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3840 (p : Pattern) (guard : d1016 p = 1) : d456 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d456, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3830 p hg
    simpa only [d456, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d456, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d456, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3841 (p : Pattern) (guard : d1016 p = 1) : d457 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d457, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3834 p hg
    simpa only [d457, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d457, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2205 p hg
    simpa only [d457, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3842 (p : Pattern) (guard : d1016 p = 1) : d458 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d458, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3840 p hg
    simpa only [d458, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d458, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3841 p hg
    simpa only [d458, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3843 (p : Pattern) (guard : d1016 p = 1) : d459 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d459, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3836 p hg
    simpa only [d459, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d459, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d459, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3844 (p : Pattern) (guard : d1016 p = 1) : d460 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d460, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3837 p hg
    simpa only [d460, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d460, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2205 p hg
    simpa only [d460, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3845 (p : Pattern) (guard : d1016 p = 1) : d461 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d461, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3843 p hg
    simpa only [d461, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d461, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3844 p hg
    simpa only [d461, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3846 (p : Pattern) (guard : d1016 p = 1) : d462 p ≤ (0 : Int) + d231 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3842 p hg
    simpa only [d462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3845 p hg
    simpa only [d462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3847 (p : Pattern) (guard : d1016 p = 1) : d463 p ≤ (0 : Int) + d366 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d463, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3839 p hg
    simpa only [d463, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d463, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3846 p hg
    simpa only [d463, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3848 (p : Pattern) (guard : d1016 p = 1) : d464 p ≤ (0 : Int) + d367 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d464, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3846 p hg
    simpa only [d464, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d464, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2213 p hg
    simpa only [d464, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3849 (p : Pattern) (guard : d1016 p = 1) : d465 p ≤ (0 : Int) + d368 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d465, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3847 p hg
    simpa only [d465, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d465, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3848 p hg
    simpa only [d465, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3850 (p : Pattern) (guard : d1016 p = 1) : d466 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d466, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3829 p hg
    simpa only [d1016, d466, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d466, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1866 p hg
    simpa only [d1016, d466, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3851 (p : Pattern) (guard : d1016 p = 1) : d467 p ≤ (0 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3830 p hg
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3850 p hg
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3852 (p : Pattern) (guard : d1016 p = 1) : d468 p ≤ (0 : Int) + d106 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3830 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3851 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3853 (p : Pattern) (guard : d1016 p = 1) : d469 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d469, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3833 p hg
    simpa only [d1016, d469, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d469, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1870 p hg
    simpa only [d1016, d469, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3854 (p : Pattern) (guard : d1016 p = 1) : d470 p ≤ (0 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3834 p hg
    simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3853 p hg
    simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3855 (p : Pattern) (guard : d1016 p = 1) : d471 p ≤ (0 : Int) + d109 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3834 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3854 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3856 (p : Pattern) (guard : d1016 p = 1) : d472 p ≤ (0 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d472, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3852 p hg
    simpa only [d472, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d472, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3855 p hg
    simpa only [d472, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3857 (p : Pattern) (guard : d1016 p = 1) : d473 p ≤ (0 : Int) + d369 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d473, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3856 p hg
    simpa only [d473, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d473, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2213 p hg
    simpa only [d473, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3858 (p : Pattern) (guard : d1016 p = 1) : d474 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d474, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3850 p hg
    simpa only [d474, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d474, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d474, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3859 (p : Pattern) (guard : d1016 p = 1) : d475 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d475, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3853 p hg
    simpa only [d475, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d475, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2205 p hg
    simpa only [d475, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3860 (p : Pattern) (guard : d1016 p = 1) : d476 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d476, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3858 p hg
    simpa only [d476, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d476, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3859 p hg
    simpa only [d476, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3861 (p : Pattern) (guard : d1016 p = 1) : d477 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d477, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3860 p hg
    simpa only [d477, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d477, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2213 p hg
    simpa only [d477, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3862 (p : Pattern) (guard : d1016 p = 1) : d478 p ≤ (0 : Int) + d371 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d478, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3857 p hg
    simpa only [d478, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d478, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3861 p hg
    simpa only [d478, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3863 (p : Pattern) (guard : d1016 p = 1) : d479 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d479, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3851 p hg
    simpa only [d479, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d479, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d479, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3864 (p : Pattern) (guard : d1016 p = 1) : d480 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d480, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3854 p hg
    simpa only [d480, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d480, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2205 p hg
    simpa only [d480, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3865 (p : Pattern) (guard : d1016 p = 1) : d481 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d481, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3863 p hg
    simpa only [d481, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d481, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3864 p hg
    simpa only [d481, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3866 (p : Pattern) (guard : d1016 p = 1) : d482 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d482, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3865 p hg
    simpa only [d482, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d482, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2213 p hg
    simpa only [d482, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3867 (p : Pattern) (guard : d1016 p = 1) : d483 p ≤ (0 : Int) + d372 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d483, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3866 p hg
    simpa only [d483, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d483, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2213 p hg
    simpa only [d483, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3868 (p : Pattern) (guard : d1016 p = 1) : d484 p ≤ (0 : Int) + d373 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d484, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3862 p hg
    simpa only [d484, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d484, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3867 p hg
    simpa only [d484, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3869 (p : Pattern) (guard : d1016 p = 1) : d485 p ≤ (0 : Int) + d374 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d485, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3849 p hg
    simpa only [d485, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d485, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3868 p hg
    simpa only [d485, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3870 (p : Pattern) (guard : d0 p = 1) : d56 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3871 (p : Pattern) (guard : d830 p = 1) : d56 p ≤ (0 : Int) + d7 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3870 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3829 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3872 (p : Pattern) (guard : d0 p = 1) : d62 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3873 (p : Pattern) (guard : d830 p = 1) : d62 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3872 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3833 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3874 (p : Pattern) (guard : d830 p = 1) : d451 p ≤ (0 : Int) + d13 p := by
  cases selected : p 141 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d451, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3871 p hg
    simpa only [d451, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d451, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3873 p hg
    simpa only [d451, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3875 (p : Pattern) (guard : d0 p = 1) : d454 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3876 (p : Pattern) (guard : d831 p = 1) : d455 p ≤ (0 : Int) + d13 p := by
  cases selected : p 134 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d831, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3874 p hg
    simpa only [d831, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d831, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3875 p hg
    simpa only [d831, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3877 (p : Pattern) (guard : d830 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  omega
theorem compare3878 (p : Pattern) (guard : d830 p = 1) : d456 p ≤ (0 : Int) + d832 p := by
  cases selected : p 158 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d456, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3871 p hg
    simpa only [d456, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d456, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3877 p hg
    simpa only [d456, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3879 (p : Pattern) (guard : d830 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  omega
theorem compare3880 (p : Pattern) (guard : d830 p = 1) : d457 p ≤ (0 : Int) + d833 p := by
  cases selected : p 158 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d457, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3873 p hg
    simpa only [d457, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d457, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3879 p hg
    simpa only [d457, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3881 (p : Pattern) (guard : d830 p = 1) : d458 p ≤ (0 : Int) + d834 p := by
  cases selected : p 141 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d458, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3878 p hg
    simpa only [d458, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d458, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3880 p hg
    simpa only [d458, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3882 (p : Pattern) (guard : d0 p = 1) : d461 p ≤ (0 : Int) + d834 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3883 (p : Pattern) (guard : d831 p = 1) : d462 p ≤ (0 : Int) + d834 p := by
  cases selected : p 134 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d831, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3881 p hg
    simpa only [d831, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d831, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3882 p hg
    simpa only [d831, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3884 (p : Pattern) (guard : d831 p = 1) : d463 p ≤ (0 : Int) + d835 p := by
  cases selected : p 133 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d463, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3876 p hg
    simpa only [d463, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d831 p = 1 := by simpa only [d463, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3883 p hg
    simpa only [d463, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3885 (p : Pattern) (guard : d831 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare3886 (p : Pattern) (guard : d831 p = 1) : d464 p ≤ (0 : Int) + d836 p := by
  cases selected : p 133 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d464, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3883 p hg
    simpa only [d464, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d831 p = 1 := by simpa only [d464, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3885 p hg
    simpa only [d464, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3887 (p : Pattern) (guard : d831 p = 1) : d465 p ≤ (0 : Int) + d837 p := by
  cases selected : p 132 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d465, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3884 p hg
    simpa only [d465, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d831 p = 1 := by simpa only [d465, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3886 p hg
    simpa only [d465, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3888 (p : Pattern) (guard : d830 p = 1) : d56 p ≤ (0 : Int) + d55 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare684 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3492 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3889 (p : Pattern) (guard : d830 p = 1) : d466 p ≤ (0 : Int) + d55 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d830, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare684 p hg
    simpa only [d830, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d830, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3524 p hg
    simpa only [d830, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3890 (p : Pattern) (guard : d830 p = 1) : d467 p ≤ (0 : Int) + d55 p := by
  cases selected : p 159 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3888 p hg
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3889 p hg
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3891 (p : Pattern) (guard : d830 p = 1) : d468 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3888 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3890 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3892 (p : Pattern) (guard : d830 p = 1) : d62 p ≤ (0 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare686 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3495 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3893 (p : Pattern) (guard : d830 p = 1) : d469 p ≤ (0 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d830, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare686 p hg
    simpa only [d830, d469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d830, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3529 p hg
    simpa only [d830, d469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3894 (p : Pattern) (guard : d830 p = 1) : d470 p ≤ (0 : Int) + d65 p := by
  cases selected : p 159 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3892 p hg
    simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3893 p hg
    simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3895 (p : Pattern) (guard : d830 p = 1) : d471 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3892 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3894 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3896 (p : Pattern) (guard : d830 p = 1) : d472 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d472, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3891 p hg
    simpa only [d472, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d472, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3895 p hg
    simpa only [d472, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3897 (p : Pattern) (guard : d831 p = 1) : d473 p ≤ (0 : Int) + d66 p := by
  cases selected : p 134 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d831, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3896 p hg
    simpa only [d831, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d831, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d831, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3898 (p : Pattern) (guard : d830 p = 1) : d474 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3889 p hg
    simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3877 p hg
    simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3899 (p : Pattern) (guard : d830 p = 1) : d475 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3893 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3879 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3900 (p : Pattern) (guard : d830 p = 1) : d476 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d476, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3898 p hg
    simpa only [d476, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d476, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3899 p hg
    simpa only [d476, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3901 (p : Pattern) (guard : d831 p = 1) : d477 p ≤ (0 : Int) + d66 p := by
  cases selected : p 134 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d831, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3900 p hg
    simpa only [d831, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d831, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d831, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3902 (p : Pattern) (guard : d831 p = 1) : d478 p ≤ (0 : Int) + d66 p := by
  cases selected : p 133 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3897 p hg
    simpa only [d478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d831 p = 1 := by simpa only [d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3901 p hg
    simpa only [d478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3903 (p : Pattern) (guard : d830 p = 1) : d479 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3890 p hg
    simpa only [d479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3877 p hg
    simpa only [d479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3904 (p : Pattern) (guard : d830 p = 1) : d480 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3894 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3879 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3905 (p : Pattern) (guard : d830 p = 1) : d481 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d481, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3903 p hg
    simpa only [d481, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d481, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3904 p hg
    simpa only [d481, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3906 (p : Pattern) (guard : d831 p = 1) : d482 p ≤ (0 : Int) + d66 p := by
  cases selected : p 134 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d831, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3905 p hg
    simpa only [d831, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d831, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d831, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3907 (p : Pattern) (guard : d831 p = 1) : d483 p ≤ (0 : Int) + d66 p := by
  cases selected : p 133 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3906 p hg
    simpa only [d483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d831 p = 1 := by simpa only [d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3885 p hg
    simpa only [d483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3908 (p : Pattern) (guard : d831 p = 1) : d484 p ≤ (0 : Int) + d66 p := by
  cases selected : p 132 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3902 p hg
    simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d831 p = 1 := by simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3907 p hg
    simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3909 (p : Pattern) (guard : d831 p = 1) : d485 p ≤ (0 : Int) + d1173 p := by
  cases selected : p 108 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d485, d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3887 p hg
    simpa only [d485, d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d831 p = 1 := by simpa only [d485, d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3908 p hg
    simpa only [d485, d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3910 (p : Pattern) (guard : d829 p = 1) : d56 p ≤ (0 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3829 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2110 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3911 (p : Pattern) (guard : d829 p = 1) : d62 p ≤ (0 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3833 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2116 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3912 (p : Pattern) (guard : d829 p = 1) : d451 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d451, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3910 p hg
    simpa only [d451, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d451, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3911 p hg
    simpa only [d451, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3913 (p : Pattern) (guard : d829 p = 1) : d452 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d452, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3829 p hg
    simpa only [d452, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d452, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d452, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3914 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d119 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3915 (p : Pattern) (guard : d829 p = 1) : d56 p ≤ (0 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d56, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d829, d56, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d56, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3914 p hg
    simpa only [d829, d56, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3916 (p : Pattern) (guard : d829 p = 1) : d452 p ≤ (0 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d452, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3915 p hg
    simpa only [d452, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d452, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d452, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3917 (p : Pattern) (guard : d829 p = 1) : d452 p ≤ (0 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3913 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3916 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3918 (p : Pattern) (guard : d829 p = 1) : d452 p ≤ (0 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3913 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3917 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3919 (p : Pattern) (guard : d829 p = 1) : d453 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d453, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3833 p hg
    simpa only [d453, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d453, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d453, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
