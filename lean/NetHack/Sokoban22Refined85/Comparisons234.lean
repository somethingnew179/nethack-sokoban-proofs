/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons233
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare32760 (p : Pattern) (guard : d6558 p = 1) : d1728 p ≤ (2 : Int) + d7286 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1728, d7286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32756 p hg
    simpa only [d1728, d7286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1728, d7286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32759 p hg
    simpa only [d1728, d7286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32761 (p : Pattern) (guard : d6558 p = 1) : d1729 p ≤ (2 : Int) + d7287 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1729, d7287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32760 p hg
    simpa only [d1729, d7287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1729, d7287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32759 p hg
    simpa only [d1729, d7287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32762 (p : Pattern) (guard : d6558 p = 1) : d1730 p ≤ (2 : Int) + d7288 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1730, d7288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32761 p hg
    simpa only [d1730, d7288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1730, d7288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1730, d7288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32763 (p : Pattern) (guard : d6558 p = 1) : d2910 p ≤ (2 : Int) + d7289 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2910, d7289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32723 p hg
    simpa only [d2910, d7289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2910, d7289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32762 p hg
    simpa only [d2910, d7289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32764 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (2 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32765 (p : Pattern) (guard : d5842 p = 1) : d1791 p ≤ (2 : Int) + d10 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32764 p hg
    simpa only [d5842, d1791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15723 p hg
    simpa only [d5842, d1791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32766 (p : Pattern) (guard : d6558 p = 1) : d1792 p ≤ (2 : Int) + d10 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32765 p hg
    simpa only [d6558, d1792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32748 p hg
    simpa only [d6558, d1792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32767 (p : Pattern) (guard : d6558 p = 1) : d1793 p ≤ (2 : Int) + d7290 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1793, d7290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32676 p hg
    simpa only [d1793, d7290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1793, d7290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32766 p hg
    simpa only [d1793, d7290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32768 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32769 (p : Pattern) (guard : d5842 p = 1) : d17 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32768 p hg
    simpa only [d5842, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d5842, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32770 (p : Pattern) (guard : d6558 p = 1) : d339 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32769 p hg
    simpa only [d6558, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d6558, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32771 (p : Pattern) (guard : d6558 p = 1) : d1796 p ≤ (2 : Int) + d7291 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1796, d7291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32680 p hg
    simpa only [d1796, d7291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1796, d7291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32770 p hg
    simpa only [d1796, d7291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32772 (p : Pattern) (guard : d6558 p = 1) : d1797 p ≤ (2 : Int) + d7292 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1797, d7292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32767 p hg
    simpa only [d1797, d7292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1797, d7292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32771 p hg
    simpa only [d1797, d7292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32773 (p : Pattern) (guard : d6558 p = 1) : d2911 p ≤ (2 : Int) + d7293 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2911, d7293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32676 p hg
    simpa only [d2911, d7293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2911, d7293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32772 p hg
    simpa only [d2911, d7293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32774 (p : Pattern) (guard : d6558 p = 1) : d2912 p ≤ (2 : Int) + d7294 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2912, d7294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32773 p hg
    simpa only [d2912, d7294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2912, d7294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2912, d7294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32775 (p : Pattern) (guard : d6558 p = 1) : d2913 p ≤ (2 : Int) + d7295 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2913, d7295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32763 p hg
    simpa only [d2913, d7295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2913, d7295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32774 p hg
    simpa only [d2913, d7295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32776 (p : Pattern) (guard : d6558 p = 1) : d2914 p ≤ (2 : Int) + d7296 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2914, d7296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32754 p hg
    simpa only [d2914, d7296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2914, d7296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32775 p hg
    simpa only [d2914, d7296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32777 (p : Pattern) (guard : d6558 p = 1) : d2915 p ≤ (2 : Int) + d7297 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2915, d7297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32723 p hg
    simpa only [d2915, d7297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2915, d7297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2915, d7297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32778 (p : Pattern) (guard : d6558 p = 1) : d2916 p ≤ (2 : Int) + d7298 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2916, d7298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32777 p hg
    simpa only [d2916, d7298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2916, d7298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32774 p hg
    simpa only [d2916, d7298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32779 (p : Pattern) (guard : d6558 p = 1) : d2917 p ≤ (2 : Int) + d7299 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2917, d7299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32702 p hg
    simpa only [d2917, d7299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2917, d7299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2917, d7299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32780 (p : Pattern) (guard : d6558 p = 1) : d2918 p ≤ (2 : Int) + d7300 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2918, d7300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32779 p hg
    simpa only [d2918, d7300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2918, d7300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2918, d7300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32781 (p : Pattern) (guard : d6558 p = 1) : d2919 p ≤ (2 : Int) + d7301 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2919, d7301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32778 p hg
    simpa only [d2919, d7301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2919, d7301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32780 p hg
    simpa only [d2919, d7301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32782 (p : Pattern) (guard : d6558 p = 1) : d2920 p ≤ (2 : Int) + d7302 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2920, d7302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32776 p hg
    simpa only [d2920, d7302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2920, d7302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32781 p hg
    simpa only [d2920, d7302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32783 (p : Pattern) (guard : d6558 p = 1) : d2921 p ≤ (2 : Int) + d7303 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2921, d7303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32713 p hg
    simpa only [d2921, d7303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2921, d7303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32782 p hg
    simpa only [d2921, d7303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32784 (p : Pattern) (guard : d6558 p = 1) : d2029 p ≤ (2 : Int) + d7304 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2029, d7304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32725 p hg
    simpa only [d2029, d7304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2029, d7304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32732 p hg
    simpa only [d2029, d7304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32785 (p : Pattern) (guard : d6558 p = 1) : d2030 p ≤ (2 : Int) + d7305 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2030, d7305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32784 p hg
    simpa only [d2030, d7305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2030, d7305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32732 p hg
    simpa only [d2030, d7305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32786 (p : Pattern) (guard : d6558 p = 1) : d2922 p ≤ (2 : Int) + d7306 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2922, d7306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32725 p hg
    simpa only [d2922, d7306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2922, d7306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32785 p hg
    simpa only [d2922, d7306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32787 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32788 (p : Pattern) (guard : d5842 p = 1) : d1742 p ≤ (2 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32787 p hg
    simpa only [d5842, d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15683 p hg
    simpa only [d5842, d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32789 (p : Pattern) (guard : d6558 p = 1) : d1743 p ≤ (2 : Int) + d4 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32788 p hg
    simpa only [d6558, d1743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32661 p hg
    simpa only [d6558, d1743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32790 (p : Pattern) (guard : d6558 p = 1) : d1744 p ≤ (2 : Int) + d7307 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1744, d7307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32725 p hg
    simpa only [d1744, d7307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1744, d7307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32789 p hg
    simpa only [d1744, d7307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32791 (p : Pattern) (guard : d6558 p = 1) : d1745 p ≤ (2 : Int) + d7308 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1745, d7308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32790 p hg
    simpa only [d1745, d7308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1745, d7308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32789 p hg
    simpa only [d1745, d7308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32792 (p : Pattern) (guard : d6558 p = 1) : d1746 p ≤ (2 : Int) + d7309 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1746, d7309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32791 p hg
    simpa only [d1746, d7309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1746, d7309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1746, d7309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32793 (p : Pattern) (guard : d6558 p = 1) : d2923 p ≤ (2 : Int) + d7310 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2923, d7310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32786 p hg
    simpa only [d2923, d7310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2923, d7310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32792 p hg
    simpa only [d2923, d7310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32794 (p : Pattern) (guard : d6558 p = 1) : d2924 p ≤ (2 : Int) + d7311 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2924, d7311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32674 p hg
    simpa only [d2924, d7311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2924, d7311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32793 p hg
    simpa only [d2924, d7311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32795 (p : Pattern) (guard : d6558 p = 1) : d2925 p ≤ (2 : Int) + d7312 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2925, d7312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32691 p hg
    simpa only [d2925, d7312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2925, d7312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32710 p hg
    simpa only [d2925, d7312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32796 (p : Pattern) (guard : d6558 p = 1) : d2926 p ≤ (2 : Int) + d7313 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2926, d7313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32794 p hg
    simpa only [d2926, d7313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2926, d7313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32795 p hg
    simpa only [d2926, d7313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32797 (p : Pattern) (guard : d5842 p = 1) : d10 p ≤ (2 : Int) + d10 p := by
  omega
theorem compare32798 (p : Pattern) (guard : d6558 p = 1) : d58 p ≤ (2 : Int) + d10 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32797 p hg
    simpa only [d6558, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32748 p hg
    simpa only [d6558, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32799 (p : Pattern) (guard : d0 p = 1) : d10 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32800 (p : Pattern) (guard : d5842 p = 1) : d57 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32799 p hg
    simpa only [d5842, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d5842, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32801 (p : Pattern) (guard : d6558 p = 1) : d329 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32800 p hg
    simpa only [d6558, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d6558, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32802 (p : Pattern) (guard : d6558 p = 1) : d1751 p ≤ (2 : Int) + d7281 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1751, d7281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32798 p hg
    simpa only [d1751, d7281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1751, d7281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32801 p hg
    simpa only [d1751, d7281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32803 (p : Pattern) (guard : d6558 p = 1) : d1752 p ≤ (2 : Int) + d7314 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1752, d7314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32802 p hg
    simpa only [d1752, d7314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1752, d7314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32801 p hg
    simpa only [d1752, d7314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32804 (p : Pattern) (guard : d6558 p = 1) : d2927 p ≤ (2 : Int) + d7315 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2927, d7315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32798 p hg
    simpa only [d2927, d7315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2927, d7315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32803 p hg
    simpa only [d2927, d7315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32805 (p : Pattern) (guard : d6558 p = 1) : d1753 p ≤ (2 : Int) + d7316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1753, d7316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32803 p hg
    simpa only [d1753, d7316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1753, d7316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1753, d7316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32806 (p : Pattern) (guard : d6558 p = 1) : d2928 p ≤ (2 : Int) + d7317 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2928, d7317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32804 p hg
    simpa only [d2928, d7317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2928, d7317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32805 p hg
    simpa only [d2928, d7317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32807 (p : Pattern) (guard : d6558 p = 1) : d2929 p ≤ (2 : Int) + d7318 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2929, d7318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32691 p hg
    simpa only [d2929, d7318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2929, d7318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32806 p hg
    simpa only [d2929, d7318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32808 (p : Pattern) (guard : d6558 p = 1) : d2930 p ≤ (2 : Int) + d7319 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2930, d7319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32756 p hg
    simpa only [d2930, d7319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2930, d7319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32761 p hg
    simpa only [d2930, d7319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32809 (p : Pattern) (guard : d6558 p = 1) : d2931 p ≤ (2 : Int) + d7320 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2931, d7320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32808 p hg
    simpa only [d2931, d7320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2931, d7320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32762 p hg
    simpa only [d2931, d7320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32810 (p : Pattern) (guard : d6558 p = 1) : d2932 p ≤ (2 : Int) + d7321 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2932, d7321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32809 p hg
    simpa only [d2932, d7321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2932, d7321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2932, d7321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32811 (p : Pattern) (guard : d6558 p = 1) : d2933 p ≤ (2 : Int) + d7322 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2933, d7322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32807 p hg
    simpa only [d2933, d7322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2933, d7322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32810 p hg
    simpa only [d2933, d7322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32812 (p : Pattern) (guard : d6558 p = 1) : d2934 p ≤ (2 : Int) + d7323 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2934, d7323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32796 p hg
    simpa only [d2934, d7323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2934, d7323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32811 p hg
    simpa only [d2934, d7323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32813 (p : Pattern) (guard : d6558 p = 1) : d2935 p ≤ (2 : Int) + d7324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2935, d7324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32725 p hg
    simpa only [d2935, d7324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2935, d7324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32737 p hg
    simpa only [d2935, d7324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32814 (p : Pattern) (guard : d6558 p = 1) : d2936 p ≤ (2 : Int) + d7325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2936, d7325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32813 p hg
    simpa only [d2936, d7325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2936, d7325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2936, d7325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32815 (p : Pattern) (guard : d6558 p = 1) : d2937 p ≤ (2 : Int) + d7326 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2937, d7326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32753 p hg
    simpa only [d2937, d7326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2937, d7326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32814 p hg
    simpa only [d2937, d7326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32816 (p : Pattern) (guard : d6558 p = 1) : d2938 p ≤ (2 : Int) + d7327 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2938, d7327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32774 p hg
    simpa only [d2938, d7327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2938, d7327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32779 p hg
    simpa only [d2938, d7327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32817 (p : Pattern) (guard : d6558 p = 1) : d2939 p ≤ (2 : Int) + d7328 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2939, d7328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32815 p hg
    simpa only [d2939, d7328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2939, d7328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32816 p hg
    simpa only [d2939, d7328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32818 (p : Pattern) (guard : d6558 p = 1) : d2940 p ≤ (2 : Int) + d7329 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2940, d7329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32804 p hg
    simpa only [d2940, d7329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2940, d7329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2940, d7329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32819 (p : Pattern) (guard : d6558 p = 1) : d2941 p ≤ (2 : Int) + d7330 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2941, d7330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32774 p hg
    simpa only [d2941, d7330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2941, d7330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32818 p hg
    simpa only [d2941, d7330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32820 (p : Pattern) (guard : d6558 p = 1) : d2942 p ≤ (2 : Int) + d7331 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2942, d7331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32808 p hg
    simpa only [d2942, d7331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2942, d7331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2942, d7331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32821 (p : Pattern) (guard : d6558 p = 1) : d2943 p ≤ (2 : Int) + d7332 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2943, d7332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32820 p hg
    simpa only [d2943, d7332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2943, d7332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2943, d7332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32822 (p : Pattern) (guard : d6558 p = 1) : d2944 p ≤ (2 : Int) + d7333 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2944, d7333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32819 p hg
    simpa only [d2944, d7333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2944, d7333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32821 p hg
    simpa only [d2944, d7333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32823 (p : Pattern) (guard : d6558 p = 1) : d2945 p ≤ (2 : Int) + d7334 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2945, d7334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32817 p hg
    simpa only [d2945, d7334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2945, d7334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32822 p hg
    simpa only [d2945, d7334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32824 (p : Pattern) (guard : d6558 p = 1) : d2946 p ≤ (2 : Int) + d7335 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2946, d7335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32812 p hg
    simpa only [d2946, d7335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2946, d7335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32823 p hg
    simpa only [d2946, d7335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32825 (p : Pattern) (guard : d6558 p = 1) : d2947 p ≤ (2 : Int) + d7336 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2947, d7336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32783 p hg
    simpa only [d2947, d7336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2947, d7336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32824 p hg
    simpa only [d2947, d7336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32826 (p : Pattern) (guard : d6558 p = 1) : d2047 p ≤ (2 : Int) + d7255 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2047, d7255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32662 p hg
    simpa only [d2047, d7255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2047, d7255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32716 p hg
    simpa only [d2047, d7255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32827 (p : Pattern) (guard : d6558 p = 1) : d2048 p ≤ (2 : Int) + d7337 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2048, d7337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32717 p hg
    simpa only [d2048, d7337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2048, d7337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32826 p hg
    simpa only [d2048, d7337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32828 (p : Pattern) (guard : d6558 p = 1) : d2948 p ≤ (2 : Int) + d7338 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2948, d7338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32658 p hg
    simpa only [d2948, d7338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2948, d7338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32827 p hg
    simpa only [d2948, d7338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32829 (p : Pattern) (guard : d6558 p = 1) : d1773 p ≤ (2 : Int) + d7339 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1773, d7339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32664 p hg
    simpa only [d1773, d7339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1773, d7339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1773, d7339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32830 (p : Pattern) (guard : d6558 p = 1) : d2949 p ≤ (2 : Int) + d7340 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2949, d7340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32828 p hg
    simpa only [d2949, d7340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2949, d7340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32829 p hg
    simpa only [d2949, d7340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32831 (p : Pattern) (guard : d5842 p = 1) : d2051 p ≤ (2 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32718 p hg
    simpa only [d5842, d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6017 p hg
    simpa only [d5842, d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32832 (p : Pattern) (guard : d6558 p = 1) : d2052 p ≤ (2 : Int) + d9 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32831 p hg
    simpa only [d6558, d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32695 p hg
    simpa only [d6558, d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32833 (p : Pattern) (guard : d6558 p = 1) : d2053 p ≤ (2 : Int) + d7272 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2053, d7272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32662 p hg
    simpa only [d2053, d7272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2053, d7272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32832 p hg
    simpa only [d2053, d7272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32834 (p : Pattern) (guard : d6558 p = 1) : d2054 p ≤ (2 : Int) + d7273 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2054, d7273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32717 p hg
    simpa only [d2054, d7273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2054, d7273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32833 p hg
    simpa only [d2054, d7273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32835 (p : Pattern) (guard : d6558 p = 1) : d2950 p ≤ (2 : Int) + d7274 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2950, d7274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32658 p hg
    simpa only [d2950, d7274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2950, d7274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32834 p hg
    simpa only [d2950, d7274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32836 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (2 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32837 (p : Pattern) (guard : d5842 p = 1) : d1778 p ≤ (2 : Int) + d8 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32836 p hg
    simpa only [d5842, d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16154 p hg
    simpa only [d5842, d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32838 (p : Pattern) (guard : d6558 p = 1) : d1779 p ≤ (2 : Int) + d8 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32837 p hg
    simpa only [d6558, d1779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32679 p hg
    simpa only [d6558, d1779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32839 (p : Pattern) (guard : d6558 p = 1) : d1780 p ≤ (2 : Int) + d7252 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1780, d7252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32662 p hg
    simpa only [d1780, d7252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1780, d7252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32838 p hg
    simpa only [d1780, d7252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32840 (p : Pattern) (guard : d6558 p = 1) : d1781 p ≤ (2 : Int) + d7341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1781, d7341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32717 p hg
    simpa only [d1781, d7341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1781, d7341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32839 p hg
    simpa only [d1781, d7341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32841 (p : Pattern) (guard : d6558 p = 1) : d1782 p ≤ (2 : Int) + d7342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1782, d7342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32840 p hg
    simpa only [d1782, d7342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1782, d7342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1782, d7342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32842 (p : Pattern) (guard : d6558 p = 1) : d2951 p ≤ (2 : Int) + d7343 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2951, d7343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32835 p hg
    simpa only [d2951, d7343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2951, d7343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32841 p hg
    simpa only [d2951, d7343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32843 (p : Pattern) (guard : d6558 p = 1) : d2952 p ≤ (2 : Int) + d7344 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2952, d7344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32830 p hg
    simpa only [d2952, d7344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2952, d7344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32842 p hg
    simpa only [d2952, d7344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32844 (p : Pattern) (guard : d6558 p = 1) : d1789 p ≤ (2 : Int) + d7345 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1789, d7345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32722 p hg
    simpa only [d1789, d7345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1789, d7345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1789, d7345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32845 (p : Pattern) (guard : d6558 p = 1) : d2953 p ≤ (2 : Int) + d7346 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2953, d7346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32723 p hg
    simpa only [d2953, d7346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2953, d7346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32844 p hg
    simpa only [d2953, d7346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32846 (p : Pattern) (guard : d6558 p = 1) : d1798 p ≤ (2 : Int) + d7347 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1798, d7347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32772 p hg
    simpa only [d1798, d7347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1798, d7347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1798, d7347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32847 (p : Pattern) (guard : d6558 p = 1) : d2954 p ≤ (2 : Int) + d7348 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2954, d7348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32773 p hg
    simpa only [d2954, d7348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2954, d7348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32846 p hg
    simpa only [d2954, d7348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32848 (p : Pattern) (guard : d6558 p = 1) : d2955 p ≤ (2 : Int) + d7349 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2955, d7349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32845 p hg
    simpa only [d2955, d7349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2955, d7349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32847 p hg
    simpa only [d2955, d7349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32849 (p : Pattern) (guard : d6558 p = 1) : d2956 p ≤ (2 : Int) + d7350 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2956, d7350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32843 p hg
    simpa only [d2956, d7350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2956, d7350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32848 p hg
    simpa only [d2956, d7350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32850 (p : Pattern) (guard : d6558 p = 1) : d1804 p ≤ (2 : Int) + d7351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1804, d7351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32701 p hg
    simpa only [d1804, d7351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1804, d7351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1804, d7351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32851 (p : Pattern) (guard : d6558 p = 1) : d2957 p ≤ (2 : Int) + d7352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2957, d7352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32702 p hg
    simpa only [d2957, d7352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2957, d7352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32850 p hg
    simpa only [d2957, d7352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32852 (p : Pattern) (guard : d6558 p = 1) : d2958 p ≤ (2 : Int) + d7353 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2958, d7353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32851 p hg
    simpa only [d2958, d7353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2958, d7353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2958, d7353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32853 (p : Pattern) (guard : d6558 p = 1) : d2959 p ≤ (2 : Int) + d7354 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2959, d7354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32848 p hg
    simpa only [d2959, d7354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2959, d7354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32852 p hg
    simpa only [d2959, d7354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32854 (p : Pattern) (guard : d6558 p = 1) : d2960 p ≤ (2 : Int) + d7355 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2960, d7355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32849 p hg
    simpa only [d2960, d7355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2960, d7355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32853 p hg
    simpa only [d2960, d7355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32855 (p : Pattern) (guard : d6558 p = 1) : d2961 p ≤ (2 : Int) + d7356 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2961, d7356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32813 p hg
    simpa only [d2961, d7356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2961, d7356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32738 p hg
    simpa only [d2961, d7356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32856 (p : Pattern) (guard : d6558 p = 1) : d2962 p ≤ (2 : Int) + d7357 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2962, d7357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32741 p hg
    simpa only [d2962, d7357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2962, d7357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32751 p hg
    simpa only [d2962, d7357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32857 (p : Pattern) (guard : d6558 p = 1) : d2963 p ≤ (2 : Int) + d7358 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2963, d7358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32856 p hg
    simpa only [d2963, d7358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2963, d7358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32752 p hg
    simpa only [d2963, d7358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32858 (p : Pattern) (guard : d6558 p = 1) : d2964 p ≤ (2 : Int) + d7359 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2964, d7359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32855 p hg
    simpa only [d2964, d7359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2964, d7359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32857 p hg
    simpa only [d2964, d7359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32859 (p : Pattern) (guard : d6558 p = 1) : d2965 p ≤ (2 : Int) + d7360 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2965, d7360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32858 p hg
    simpa only [d2965, d7360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2965, d7360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32810 p hg
    simpa only [d2965, d7360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32860 (p : Pattern) (guard : d6558 p = 1) : d2966 p ≤ (2 : Int) + d7361 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2966, d7361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32859 p hg
    simpa only [d2966, d7361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2966, d7361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2966, d7361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32861 (p : Pattern) (guard : d6558 p = 1) : d2967 p ≤ (2 : Int) + d7362 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2967, d7362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32854 p hg
    simpa only [d2967, d7362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2967, d7362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32860 p hg
    simpa only [d2967, d7362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32862 (p : Pattern) (guard : d6558 p = 1) : d2968 p ≤ (2 : Int) + d7363 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2968, d7363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32842 p hg
    simpa only [d2968, d7363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2968, d7363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32855 p hg
    simpa only [d2968, d7363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32863 (p : Pattern) (guard : d6558 p = 1) : d2969 p ≤ (2 : Int) + d7364 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2969, d7364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32847 p hg
    simpa only [d2969, d7364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2969, d7364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32851 p hg
    simpa only [d2969, d7364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32864 (p : Pattern) (guard : d6558 p = 1) : d2970 p ≤ (2 : Int) + d7365 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2970, d7365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32862 p hg
    simpa only [d2970, d7365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2970, d7365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32863 p hg
    simpa only [d2970, d7365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32865 (p : Pattern) (guard : d6558 p = 1) : d2971 p ≤ (2 : Int) + d7366 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2971, d7366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32847 p hg
    simpa only [d2971, d7366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2971, d7366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32806 p hg
    simpa only [d2971, d7366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32866 (p : Pattern) (guard : d6558 p = 1) : d2972 p ≤ (2 : Int) + d7367 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2972, d7367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32865 p hg
    simpa only [d2972, d7367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2972, d7367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32810 p hg
    simpa only [d2972, d7367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32867 (p : Pattern) (guard : d6558 p = 1) : d2973 p ≤ (2 : Int) + d7368 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2973, d7368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32864 p hg
    simpa only [d2973, d7368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2973, d7368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32866 p hg
    simpa only [d2973, d7368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32868 (p : Pattern) (guard : d6558 p = 1) : d2974 p ≤ (2 : Int) + d7369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2974, d7369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32857 p hg
    simpa only [d2974, d7369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2974, d7369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2974, d7369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32869 (p : Pattern) (guard : d6558 p = 1) : d2975 p ≤ (2 : Int) + d7370 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2975, d7370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32868 p hg
    simpa only [d2975, d7370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2975, d7370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2975, d7370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32870 (p : Pattern) (guard : d6558 p = 1) : d2976 p ≤ (2 : Int) + d7371 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2976, d7371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32869 p hg
    simpa only [d2976, d7371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2976, d7371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2976, d7371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32871 (p : Pattern) (guard : d6558 p = 1) : d2977 p ≤ (2 : Int) + d7372 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2977, d7372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32867 p hg
    simpa only [d2977, d7372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2977, d7372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32870 p hg
    simpa only [d2977, d7372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32872 (p : Pattern) (guard : d6558 p = 1) : d2978 p ≤ (2 : Int) + d7373 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2978, d7373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32861 p hg
    simpa only [d2978, d7373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2978, d7373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32871 p hg
    simpa only [d2978, d7373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32873 (p : Pattern) (guard : d6558 p = 1) : d2979 p ≤ (2 : Int) + d7374 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2979, d7374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32825 p hg
    simpa only [d2979, d7374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2979, d7374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32872 p hg
    simpa only [d2979, d7374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32874 (p : Pattern) (guard : d6558 p = 1) : d2980 p ≤ (2 : Int) + d7375 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2980, d7375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32851 p hg
    simpa only [d2980, d7375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2980, d7375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32809 p hg
    simpa only [d2980, d7375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32875 (p : Pattern) (guard : d6558 p = 1) : d2981 p ≤ (2 : Int) + d7376 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2981, d7376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32874 p hg
    simpa only [d2981, d7376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2981, d7376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32810 p hg
    simpa only [d2981, d7376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32876 (p : Pattern) (guard : d6558 p = 1) : d2982 p ≤ (2 : Int) + d7377 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2982, d7377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32810 p hg
    simpa only [d2982, d7377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2982, d7377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2982, d7377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32877 (p : Pattern) (guard : d6558 p = 1) : d2983 p ≤ (2 : Int) + d7378 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2983, d7378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32875 p hg
    simpa only [d2983, d7378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2983, d7378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32876 p hg
    simpa only [d2983, d7378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32878 (p : Pattern) (guard : d6558 p = 1) : d2984 p ≤ (2 : Int) + d7379 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2984, d7379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32876 p hg
    simpa only [d2984, d7379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2984, d7379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2984, d7379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32879 (p : Pattern) (guard : d6558 p = 1) : d2985 p ≤ (2 : Int) + d7380 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2985, d7380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32877 p hg
    simpa only [d2985, d7380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2985, d7380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32878 p hg
    simpa only [d2985, d7380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32880 (p : Pattern) (guard : d6558 p = 1) : d2986 p ≤ (2 : Int) + d7381 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2986, d7381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32878 p hg
    simpa only [d2986, d7381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2986, d7381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2986, d7381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32881 (p : Pattern) (guard : d6558 p = 1) : d2987 p ≤ (2 : Int) + d7382 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2987, d7382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32879 p hg
    simpa only [d2987, d7382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2987, d7382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32880 p hg
    simpa only [d2987, d7382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32882 (p : Pattern) (guard : d6558 p = 1) : d2988 p ≤ (2 : Int) + d7383 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2988, d7383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32872 p hg
    simpa only [d2988, d7383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2988, d7383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32881 p hg
    simpa only [d2988, d7383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32883 (p : Pattern) (guard : d6558 p = 1) : d2989 p ≤ (2 : Int) + d7384 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2989, d7384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32873 p hg
    simpa only [d2989, d7384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2989, d7384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32882 p hg
    simpa only [d2989, d7384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32884 (p : Pattern) (guard : d6558 p = 1) : d2990 p ≤ (2 : Int) + d7385 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2990, d7385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32872 p hg
    simpa only [d2990, d7385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2990, d7385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2990, d7385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32885 (p : Pattern) (guard : d6558 p = 1) : d2991 p ≤ (2 : Int) + d7386 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2991, d7386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32873 p hg
    simpa only [d2991, d7386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2991, d7386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32884 p hg
    simpa only [d2991, d7386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32886 (p : Pattern) (guard : d6558 p = 1) : d2992 p ≤ (2 : Int) + d7387 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2992, d7387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32883 p hg
    simpa only [d2992, d7387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2992, d7387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32885 p hg
    simpa only [d2992, d7387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32887 (p : Pattern) (guard : d5842 p = 1) : d1 p ≤ (2 : Int) + d1 p := by
  omega
theorem compare32888 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (2 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32889 (p : Pattern) (guard : d6558 p = 1) : d103 p ≤ (2 : Int) + d1 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32887 p hg
    simpa only [d6558, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32888 p hg
    simpa only [d6558, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32890 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (2 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32891 (p : Pattern) (guard : d5842 p = 1) : d1939 p ≤ (2 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32890 p hg
    simpa only [d5842, d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15933 p hg
    simpa only [d5842, d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32892 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (2 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32893 (p : Pattern) (guard : d6558 p = 1) : d1940 p ≤ (2 : Int) + d5 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32891 p hg
    simpa only [d6558, d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32892 p hg
    simpa only [d6558, d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32894 (p : Pattern) (guard : d6558 p = 1) : d1941 p ≤ (2 : Int) + d7388 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1941, d7388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32889 p hg
    simpa only [d1941, d7388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1941, d7388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32893 p hg
    simpa only [d1941, d7388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32895 (p : Pattern) (guard : d6558 p = 1) : d1942 p ≤ (2 : Int) + d7389 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1942, d7389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32894 p hg
    simpa only [d1942, d7389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1942, d7389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32893 p hg
    simpa only [d1942, d7389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32896 (p : Pattern) (guard : d6558 p = 1) : d2993 p ≤ (2 : Int) + d7390 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2993, d7390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32889 p hg
    simpa only [d2993, d7390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2993, d7390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32895 p hg
    simpa only [d2993, d7390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32897 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (2 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32898 (p : Pattern) (guard : d5842 p = 1) : d1872 p ≤ (2 : Int) + d3 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32897 p hg
    simpa only [d5842, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15951 p hg
    simpa only [d5842, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32899 (p : Pattern) (guard : d0 p = 1) : d115 p ≤ (2 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
