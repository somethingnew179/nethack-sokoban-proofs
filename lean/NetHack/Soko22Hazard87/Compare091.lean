import NetHack.Soko22Hazard87.Compare090
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare22750 (p : Pattern) (guard : d179825 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179824 p = 1 := by simpa only [d179825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22749 p hg
    simpa only [d179825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22751 (p : Pattern) (guard : d179826 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179825 p = 1 := by simpa only [d179826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22750 p hg
    simpa only [d179826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22752 (p : Pattern) (guard : d179851 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179826 p = 1 := by simpa only [d179851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22751 p hg
    simpa only [d179851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22753 (p : Pattern) (guard : d179755 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179750 p = 1 := by simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22744 p hg
    simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22754 (p : Pattern) (guard : d179756 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179755 p = 1 := by simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22753 p hg
    simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22755 (p : Pattern) (guard : d179757 p = 1) : d48356 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179756 p = 1 := by simpa only [d179757, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22754 p hg
    simpa only [d179757, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179757, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21695 p hg
    simpa only [d179757, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22756 (p : Pattern) (guard : d179758 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179758, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d179758, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179757 p = 1 := by simpa only [d179758, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22755 p hg
    simpa only [d179758, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22757 (p : Pattern) (guard : d179759 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179754 p = 1 := by simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22748 p hg
    simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179758 p = 1 := by simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22756 p hg
    simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22758 (p : Pattern) (guard : d179760 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179759 p = 1 := by simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22757 p hg
    simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22759 (p : Pattern) (guard : d179761 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179760 p = 1 := by simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22758 p hg
    simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22760 (p : Pattern) (guard : d179775 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179761 p = 1 := by simpa only [d179775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22759 p hg
    simpa only [d179775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22761 (p : Pattern) (guard : d179852 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179851 p = 1 := by simpa only [d179852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22752 p hg
    simpa only [d179852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179775 p = 1 := by simpa only [d179852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22760 p hg
    simpa only [d179852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22762 (p : Pattern) (guard : d179853 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179852 p = 1 := by simpa only [d179853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22761 p hg
    simpa only [d179853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22763 (p : Pattern) (guard : d179830 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179754 p = 1 := by simpa only [d179830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22748 p hg
    simpa only [d179830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22764 (p : Pattern) (guard : d179831 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179830 p = 1 := by simpa only [d179831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22763 p hg
    simpa only [d179831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22765 (p : Pattern) (guard : d179832 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179831 p = 1 := by simpa only [d179832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22764 p hg
    simpa only [d179832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22766 (p : Pattern) (guard : d179854 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179832 p = 1 := by simpa only [d179854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22765 p hg
    simpa only [d179854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22767 (p : Pattern) (guard : d179855 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179854 p = 1 := by simpa only [d179855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22766 p hg
    simpa only [d179855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22768 (p : Pattern) (guard : d179856 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179855 p = 1 := by simpa only [d179856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22767 p hg
    simpa only [d179856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22769 (p : Pattern) (guard : d179857 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179853 p = 1 := by simpa only [d179857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22762 p hg
    simpa only [d179857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179856 p = 1 := by simpa only [d179857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22768 p hg
    simpa only [d179857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22770 (p : Pattern) (guard : d179878 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179857 p = 1 := by simpa only [d179878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22769 p hg
    simpa only [d179878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22771 (p : Pattern) (guard : d179879 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179878 p = 1 := by simpa only [d179879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22770 p hg
    simpa only [d179879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22772 (p : Pattern) (guard : d179880 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179880, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179880, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179879 p = 1 := by simpa only [d179880, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22771 p hg
    simpa only [d179880, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22773 (p : Pattern) (guard : d179881 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179880 p = 1 := by simpa only [d179881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22772 p hg
    simpa only [d179881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22774 (p : Pattern) (guard : d179763 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179758 p = 1 := by simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22756 p hg
    simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22775 (p : Pattern) (guard : d179764 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179763 p = 1 := by simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22774 p hg
    simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22776 (p : Pattern) (guard : d179765 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179764 p = 1 := by simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22775 p hg
    simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22777 (p : Pattern) (guard : d179776 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179765 p = 1 := by simpa only [d179776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22776 p hg
    simpa only [d179776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22778 (p : Pattern) (guard : d179868 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179776 p = 1 := by simpa only [d179868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22777 p hg
    simpa only [d179868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22779 (p : Pattern) (guard : d179869 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179868 p = 1 := by simpa only [d179869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22778 p hg
    simpa only [d179869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22780 (p : Pattern) (guard : d179870 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179869 p = 1 := by simpa only [d179870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22779 p hg
    simpa only [d179870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22781 (p : Pattern) (guard : d179871 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179870 p = 1 := by simpa only [d179871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22780 p hg
    simpa only [d179871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22782 (p : Pattern) (guard : d179872 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179871 p = 1 := by simpa only [d179872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22781 p hg
    simpa only [d179872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22783 (p : Pattern) (guard : d179882 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179882, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179882, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179872 p = 1 := by simpa only [d179882, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22782 p hg
    simpa only [d179882, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22784 (p : Pattern) (guard : d179883 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179882 p = 1 := by simpa only [d179883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22783 p hg
    simpa only [d179883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22785 (p : Pattern) (guard : d179884 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179881 p = 1 := by simpa only [d179884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22773 p hg
    simpa only [d179884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179883 p = 1 := by simpa only [d179884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22784 p hg
    simpa only [d179884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22786 (p : Pattern) (guard : d179885 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179884 p = 1 := by simpa only [d179885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22785 p hg
    simpa only [d179885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22787 (p : Pattern) (guard : d179886 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d179885 p = 1 := by simpa only [d179886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22786 p hg
    simpa only [d179886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22788 (p : Pattern) (guard : d179887 p = 1) : d48359 p ≤ (1 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d179877 p = 1 := by simpa only [d179887, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22713 p hg
    simpa only [d179887, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179886 p = 1 := by simpa only [d179887, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22787 p hg
    simpa only [d179887, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22789 (p : Pattern) (guard : d179890 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare22790 (p : Pattern) (guard : d179891 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179890 p = 1 := by simpa only [d179891, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22789 p hg
    simpa only [d179891, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179891, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21719 p hg
    simpa only [d179891, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22791 (p : Pattern) (guard : d179892 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179891 p = 1 := by simpa only [d179892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22790 p hg
    simpa only [d179892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22792 (p : Pattern) (guard : d179893 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179892 p = 1 := by simpa only [d179893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22791 p hg
    simpa only [d179893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22793 (p : Pattern) (guard : d179896 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare22794 (p : Pattern) (guard : d179897 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179896 p = 1 := by simpa only [d179897, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22793 p hg
    simpa only [d179897, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179897, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21719 p hg
    simpa only [d179897, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22795 (p : Pattern) (guard : d179898 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179897 p = 1 := by simpa only [d179898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22794 p hg
    simpa only [d179898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22796 (p : Pattern) (guard : d179899 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179898 p = 1 := by simpa only [d179899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22795 p hg
    simpa only [d179899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22797 (p : Pattern) (guard : d179900 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179893 p = 1 := by simpa only [d179900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22792 p hg
    simpa only [d179900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179899 p = 1 := by simpa only [d179900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22796 p hg
    simpa only [d179900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22798 (p : Pattern) (guard : d179901 p = 1) : d48362 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179901, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d179901, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179900 p = 1 := by simpa only [d179901, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22797 p hg
    simpa only [d179901, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22799 (p : Pattern) (guard : d179902 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179902, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d179902, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179901 p = 1 := by simpa only [d179902, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22798 p hg
    simpa only [d179902, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22800 (p : Pattern) (guard : d179903 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179899 p = 1 := by simpa only [d179903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22796 p hg
    simpa only [d179903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22801 (p : Pattern) (guard : d179904 p = 1) : d48362 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179904, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d179904, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179903 p = 1 := by simpa only [d179904, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22800 p hg
    simpa only [d179904, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22802 (p : Pattern) (guard : d179905 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179905, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d179905, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179904 p = 1 := by simpa only [d179905, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22801 p hg
    simpa only [d179905, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22803 (p : Pattern) (guard : d179906 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179902 p = 1 := by simpa only [d179906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22799 p hg
    simpa only [d179906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179905 p = 1 := by simpa only [d179906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22802 p hg
    simpa only [d179906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22804 (p : Pattern) (guard : d179909 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare22805 (p : Pattern) (guard : d179910 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179909 p = 1 := by simpa only [d179910, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22804 p hg
    simpa only [d179910, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179910, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21719 p hg
    simpa only [d179910, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22806 (p : Pattern) (guard : d179911 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179910 p = 1 := by simpa only [d179911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22805 p hg
    simpa only [d179911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22807 (p : Pattern) (guard : d179912 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179911 p = 1 := by simpa only [d179912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22806 p hg
    simpa only [d179912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22808 (p : Pattern) (guard : d179913 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179899 p = 1 := by simpa only [d179913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22796 p hg
    simpa only [d179913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179912 p = 1 := by simpa only [d179913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22807 p hg
    simpa only [d179913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22809 (p : Pattern) (guard : d179914 p = 1) : d48362 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179914, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d179914, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179913 p = 1 := by simpa only [d179914, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22808 p hg
    simpa only [d179914, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22810 (p : Pattern) (guard : d179915 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179915, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d179915, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179914 p = 1 := by simpa only [d179915, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22809 p hg
    simpa only [d179915, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22811 (p : Pattern) (guard : d179916 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179912 p = 1 := by simpa only [d179916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22807 p hg
    simpa only [d179916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22812 (p : Pattern) (guard : d179917 p = 1) : d48362 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179917, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d179917, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179916 p = 1 := by simpa only [d179917, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22811 p hg
    simpa only [d179917, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22813 (p : Pattern) (guard : d179918 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179918, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d179918, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179917 p = 1 := by simpa only [d179918, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22812 p hg
    simpa only [d179918, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22814 (p : Pattern) (guard : d179919 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179915 p = 1 := by simpa only [d179919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22810 p hg
    simpa only [d179919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179918 p = 1 := by simpa only [d179919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22813 p hg
    simpa only [d179919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22815 (p : Pattern) (guard : d179920 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179906 p = 1 := by simpa only [d179920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22803 p hg
    simpa only [d179920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179919 p = 1 := by simpa only [d179920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22814 p hg
    simpa only [d179920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22816 (p : Pattern) (guard : d179921 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179920 p = 1 := by simpa only [d179921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22815 p hg
    simpa only [d179921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22817 (p : Pattern) (guard : d179922 p = 1) : d48365 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179921 p = 1 := by simpa only [d179922, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22816 p hg
    simpa only [d179922, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179922, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d179922, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22818 (p : Pattern) (guard : d179923 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179923, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179923, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179922 p = 1 := by simpa only [d179923, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22817 p hg
    simpa only [d179923, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22819 (p : Pattern) (guard : d179924 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179918 p = 1 := by simpa only [d179924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22813 p hg
    simpa only [d179924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22820 (p : Pattern) (guard : d179925 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179919 p = 1 := by simpa only [d179925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22814 p hg
    simpa only [d179925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179924 p = 1 := by simpa only [d179925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22819 p hg
    simpa only [d179925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22821 (p : Pattern) (guard : d179926 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179925 p = 1 := by simpa only [d179926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22820 p hg
    simpa only [d179926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22822 (p : Pattern) (guard : d179927 p = 1) : d48365 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179926 p = 1 := by simpa only [d179927, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22821 p hg
    simpa only [d179927, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179927, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d179927, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22823 (p : Pattern) (guard : d179928 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179928, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179928, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179927 p = 1 := by simpa only [d179928, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22822 p hg
    simpa only [d179928, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22824 (p : Pattern) (guard : d179929 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179923 p = 1 := by simpa only [d179929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22818 p hg
    simpa only [d179929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179928 p = 1 := by simpa only [d179929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22823 p hg
    simpa only [d179929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22825 (p : Pattern) (guard : d179930 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179929 p = 1 := by simpa only [d179930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22824 p hg
    simpa only [d179930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22826 (p : Pattern) (guard : d179931 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179930 p = 1 := by simpa only [d179931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22825 p hg
    simpa only [d179931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22827 (p : Pattern) (guard : d179932 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179931 p = 1 := by simpa only [d179932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22826 p hg
    simpa only [d179932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22828 (p : Pattern) (guard : d179933 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179924 p = 1 := by simpa only [d179933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22819 p hg
    simpa only [d179933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22829 (p : Pattern) (guard : d179934 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179933 p = 1 := by simpa only [d179934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22828 p hg
    simpa only [d179934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22830 (p : Pattern) (guard : d179935 p = 1) : d48365 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179934 p = 1 := by simpa only [d179935, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22829 p hg
    simpa only [d179935, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179935, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d179935, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22831 (p : Pattern) (guard : d179936 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179936, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179936, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179935 p = 1 := by simpa only [d179936, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22830 p hg
    simpa only [d179936, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22832 (p : Pattern) (guard : d179937 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179928 p = 1 := by simpa only [d179937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22823 p hg
    simpa only [d179937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179936 p = 1 := by simpa only [d179937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22831 p hg
    simpa only [d179937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22833 (p : Pattern) (guard : d179938 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179937 p = 1 := by simpa only [d179938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22832 p hg
    simpa only [d179938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22834 (p : Pattern) (guard : d179939 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179938 p = 1 := by simpa only [d179939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22833 p hg
    simpa only [d179939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22835 (p : Pattern) (guard : d179940 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179939 p = 1 := by simpa only [d179940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22834 p hg
    simpa only [d179940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22836 (p : Pattern) (guard : d179941 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179932 p = 1 := by simpa only [d179941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22827 p hg
    simpa only [d179941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179940 p = 1 := by simpa only [d179941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22835 p hg
    simpa only [d179941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22837 (p : Pattern) (guard : d179942 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179941 p = 1 := by simpa only [d179942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22836 p hg
    simpa only [d179942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22838 (p : Pattern) (guard : d179943 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179928 p = 1 := by simpa only [d179943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22823 p hg
    simpa only [d179943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22839 (p : Pattern) (guard : d179944 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179943 p = 1 := by simpa only [d179944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22838 p hg
    simpa only [d179944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22840 (p : Pattern) (guard : d179945 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179944 p = 1 := by simpa only [d179945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22839 p hg
    simpa only [d179945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22841 (p : Pattern) (guard : d179946 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179945 p = 1 := by simpa only [d179946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22840 p hg
    simpa only [d179946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22842 (p : Pattern) (guard : d179947 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179946 p = 1 := by simpa only [d179947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22841 p hg
    simpa only [d179947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22843 (p : Pattern) (guard : d179948 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179947 p = 1 := by simpa only [d179948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22842 p hg
    simpa only [d179948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22844 (p : Pattern) (guard : d179949 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179942 p = 1 := by simpa only [d179949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22837 p hg
    simpa only [d179949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179948 p = 1 := by simpa only [d179949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22843 p hg
    simpa only [d179949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22845 (p : Pattern) (guard : d179950 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179949 p = 1 := by simpa only [d179950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22844 p hg
    simpa only [d179950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22846 (p : Pattern) (guard : d179951 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179950 p = 1 := by simpa only [d179951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22845 p hg
    simpa only [d179951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22847 (p : Pattern) (guard : d179952 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179952, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179952, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179951 p = 1 := by simpa only [d179952, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22846 p hg
    simpa only [d179952, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22848 (p : Pattern) (guard : d179953 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179952 p = 1 := by simpa only [d179953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22847 p hg
    simpa only [d179953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22849 (p : Pattern) (guard : d179954 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179936 p = 1 := by simpa only [d179954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22831 p hg
    simpa only [d179954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22850 (p : Pattern) (guard : d179955 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179954 p = 1 := by simpa only [d179955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22849 p hg
    simpa only [d179955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22851 (p : Pattern) (guard : d179956 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179955 p = 1 := by simpa only [d179956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22850 p hg
    simpa only [d179956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22852 (p : Pattern) (guard : d179957 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179956 p = 1 := by simpa only [d179957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22851 p hg
    simpa only [d179957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22853 (p : Pattern) (guard : d179958 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179957 p = 1 := by simpa only [d179958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22852 p hg
    simpa only [d179958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22854 (p : Pattern) (guard : d179959 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179958 p = 1 := by simpa only [d179959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22853 p hg
    simpa only [d179959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22855 (p : Pattern) (guard : d179960 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179959 p = 1 := by simpa only [d179960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22854 p hg
    simpa only [d179960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22856 (p : Pattern) (guard : d179961 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179960 p = 1 := by simpa only [d179961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22855 p hg
    simpa only [d179961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22857 (p : Pattern) (guard : d179962 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179961 p = 1 := by simpa only [d179962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22856 p hg
    simpa only [d179962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22858 (p : Pattern) (guard : d179963 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179963, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179963, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179962 p = 1 := by simpa only [d179963, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22857 p hg
    simpa only [d179963, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22859 (p : Pattern) (guard : d179964 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179963 p = 1 := by simpa only [d179964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22858 p hg
    simpa only [d179964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22860 (p : Pattern) (guard : d179965 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179953 p = 1 := by simpa only [d179965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22848 p hg
    simpa only [d179965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179964 p = 1 := by simpa only [d179965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22859 p hg
    simpa only [d179965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22861 (p : Pattern) (guard : d179966 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179965 p = 1 := by simpa only [d179966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22860 p hg
    simpa only [d179966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22862 (p : Pattern) (guard : d179967 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d179966 p = 1 := by simpa only [d179967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22861 p hg
    simpa only [d179967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22863 (p : Pattern) (guard : d179968 p = 1) : d48387 p ≤ (1 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d179967 p = 1 := by simpa only [d179968, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22862 p hg
    simpa only [d179968, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179968, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21747 p hg
    simpa only [d179968, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22864 (p : Pattern) (guard : d179969 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d179887 p = 1 := by simpa only [d179969, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22788 p hg
    simpa only [d179969, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179968 p = 1 := by simpa only [d179969, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22863 p hg
    simpa only [d179969, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22865 (p : Pattern) (guard : d179970 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179969 p = 1 := by simpa only [d179970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22864 p hg
    simpa only [d179970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22866 (p : Pattern) (guard : d179971 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179970 p = 1 := by simpa only [d179971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22865 p hg
    simpa only [d179971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22867 (p : Pattern) (guard : d179972 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179971 p = 1 := by simpa only [d179972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22866 p hg
    simpa only [d179972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22868 (p : Pattern) (guard : d179973 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179972 p = 1 := by simpa only [d179973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22867 p hg
    simpa only [d179973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22869 (p : Pattern) (guard : d179974 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179973 p = 1 := by simpa only [d179974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22868 p hg
    simpa only [d179974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22870 (p : Pattern) (guard : d179975 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179974 p = 1 := by simpa only [d179975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22869 p hg
    simpa only [d179975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22871 (p : Pattern) (guard : d179976 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179975 p = 1 := by simpa only [d179976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22870 p hg
    simpa only [d179976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22872 (p : Pattern) (guard : d179977 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179976 p = 1 := by simpa only [d179977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22871 p hg
    simpa only [d179977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22873 (p : Pattern) (guard : d179978 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179977 p = 1 := by simpa only [d179978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22872 p hg
    simpa only [d179978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22874 (p : Pattern) (guard : d179979 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d179719 p = 1 := by simpa only [d179979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22507 p hg
    simpa only [d179979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179978 p = 1 := by simpa only [d179979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22873 p hg
    simpa only [d179979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22875 (p : Pattern) (guard : d179986 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare22876 (p : Pattern) (guard : d179987 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179986 p = 1 := by simpa only [d179987, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22875 p hg
    simpa only [d179987, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179987, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21624 p hg
    simpa only [d179987, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22877 (p : Pattern) (guard : d179988 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179987 p = 1 := by simpa only [d179988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22876 p hg
    simpa only [d179988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22878 (p : Pattern) (guard : d179989 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179988 p = 1 := by simpa only [d179989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22877 p hg
    simpa only [d179989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22879 (p : Pattern) (guard : d179996 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare22880 (p : Pattern) (guard : d179997 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179996 p = 1 := by simpa only [d179997, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22879 p hg
    simpa only [d179997, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179997, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21624 p hg
    simpa only [d179997, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22881 (p : Pattern) (guard : d179998 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179997 p = 1 := by simpa only [d179998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22880 p hg
    simpa only [d179998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22882 (p : Pattern) (guard : d179999 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179998 p = 1 := by simpa only [d179999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22881 p hg
    simpa only [d179999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22883 (p : Pattern) (guard : d180000 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179989 p = 1 := by simpa only [d180000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22878 p hg
    simpa only [d180000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179999 p = 1 := by simpa only [d180000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22882 p hg
    simpa only [d180000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22884 (p : Pattern) (guard : d180001 p = 1) : d48326 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180001, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d180001, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180000 p = 1 := by simpa only [d180001, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22883 p hg
    simpa only [d180001, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22885 (p : Pattern) (guard : d180002 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180002, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d180002, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180001 p = 1 := by simpa only [d180002, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22884 p hg
    simpa only [d180002, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22886 (p : Pattern) (guard : d180003 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179999 p = 1 := by simpa only [d180003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22882 p hg
    simpa only [d180003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d180003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22887 (p : Pattern) (guard : d180004 p = 1) : d48326 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180004, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d180004, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180003 p = 1 := by simpa only [d180004, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22886 p hg
    simpa only [d180004, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22888 (p : Pattern) (guard : d180005 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180005, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d180005, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180004 p = 1 := by simpa only [d180005, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22887 p hg
    simpa only [d180005, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22889 (p : Pattern) (guard : d180006 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180002 p = 1 := by simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22885 p hg
    simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180005 p = 1 := by simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22888 p hg
    simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22890 (p : Pattern) (guard : d180007 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180005 p = 1 := by simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22888 p hg
    simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22891 (p : Pattern) (guard : d180008 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180006 p = 1 := by simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22889 p hg
    simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180007 p = 1 := by simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22890 p hg
    simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22892 (p : Pattern) (guard : d180009 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180008 p = 1 := by simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22891 p hg
    simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22893 (p : Pattern) (guard : d180010 p = 1) : d48338 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180009 p = 1 := by simpa only [d180010, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22892 p hg
    simpa only [d180010, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180010, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d180010, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22894 (p : Pattern) (guard : d180011 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180011, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d180011, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180010 p = 1 := by simpa only [d180011, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22893 p hg
    simpa only [d180011, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22895 (p : Pattern) (guard : d180012 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180007 p = 1 := by simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22890 p hg
    simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22896 (p : Pattern) (guard : d180013 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180012 p = 1 := by simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22895 p hg
    simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22897 (p : Pattern) (guard : d180014 p = 1) : d48338 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180013 p = 1 := by simpa only [d180014, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22896 p hg
    simpa only [d180014, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180014, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d180014, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22898 (p : Pattern) (guard : d180015 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180015, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d180015, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180014 p = 1 := by simpa only [d180015, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22897 p hg
    simpa only [d180015, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22899 (p : Pattern) (guard : d180016 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180011 p = 1 := by simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22894 p hg
    simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180015 p = 1 := by simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22898 p hg
    simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22900 (p : Pattern) (guard : d180017 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180016 p = 1 := by simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22899 p hg
    simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22901 (p : Pattern) (guard : d180018 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180017 p = 1 := by simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22900 p hg
    simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22902 (p : Pattern) (guard : d180019 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180018 p = 1 := by simpa only [d180019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22901 p hg
    simpa only [d180019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22903 (p : Pattern) (guard : d180020 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180015 p = 1 := by simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22898 p hg
    simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22904 (p : Pattern) (guard : d180021 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180020 p = 1 := by simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22903 p hg
    simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22905 (p : Pattern) (guard : d180022 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180021 p = 1 := by simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22904 p hg
    simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22906 (p : Pattern) (guard : d180023 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180022 p = 1 := by simpa only [d180023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22905 p hg
    simpa only [d180023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22907 (p : Pattern) (guard : d180024 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180019 p = 1 := by simpa only [d180024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22902 p hg
    simpa only [d180024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180023 p = 1 := by simpa only [d180024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22906 p hg
    simpa only [d180024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22908 (p : Pattern) (guard : d180025 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180024 p = 1 := by simpa only [d180025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22907 p hg
    simpa only [d180025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22909 (p : Pattern) (guard : d180026 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180025 p = 1 := by simpa only [d180026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22908 p hg
    simpa only [d180026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22910 (p : Pattern) (guard : d180027 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180026 p = 1 := by simpa only [d180027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22909 p hg
    simpa only [d180027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22911 (p : Pattern) (guard : d180028 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180027 p = 1 := by simpa only [d180028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22910 p hg
    simpa only [d180028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22912 (p : Pattern) (guard : d180029 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180029, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180029, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180028 p = 1 := by simpa only [d180029, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22911 p hg
    simpa only [d180029, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22913 (p : Pattern) (guard : d180030 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d180030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180029 p = 1 := by simpa only [d180030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22912 p hg
    simpa only [d180030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22914 (p : Pattern) (guard : d180031 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180030 p = 1 := by simpa only [d180031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22913 p hg
    simpa only [d180031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d180031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22915 (p : Pattern) (guard : d180002 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180002, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d180002, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180001 p = 1 := by simpa only [d180002, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22884 p hg
    simpa only [d180002, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22916 (p : Pattern) (guard : d180005 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180005, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d180005, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180004 p = 1 := by simpa only [d180005, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22887 p hg
    simpa only [d180005, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22917 (p : Pattern) (guard : d180006 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180002 p = 1 := by simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22915 p hg
    simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180005 p = 1 := by simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22916 p hg
    simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22918 (p : Pattern) (guard : d180007 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180005 p = 1 := by simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22916 p hg
    simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22919 (p : Pattern) (guard : d180008 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180006 p = 1 := by simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22917 p hg
    simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180007 p = 1 := by simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22918 p hg
    simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22920 (p : Pattern) (guard : d180009 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180008 p = 1 := by simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22919 p hg
    simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22921 (p : Pattern) (guard : d180010 p = 1) : d48329 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180009 p = 1 := by simpa only [d180010, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22920 p hg
    simpa only [d180010, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180010, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d180010, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22922 (p : Pattern) (guard : d180011 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180011, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21648 p hg
    simpa only [d180011, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180010 p = 1 := by simpa only [d180011, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22921 p hg
    simpa only [d180011, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22923 (p : Pattern) (guard : d180012 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180007 p = 1 := by simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22918 p hg
    simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22924 (p : Pattern) (guard : d180013 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180012 p = 1 := by simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22923 p hg
    simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22925 (p : Pattern) (guard : d180014 p = 1) : d48329 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180013 p = 1 := by simpa only [d180014, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22924 p hg
    simpa only [d180014, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180014, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d180014, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22926 (p : Pattern) (guard : d180015 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180015, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21648 p hg
    simpa only [d180015, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180014 p = 1 := by simpa only [d180015, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22925 p hg
    simpa only [d180015, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22927 (p : Pattern) (guard : d180016 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180011 p = 1 := by simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22922 p hg
    simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180015 p = 1 := by simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22926 p hg
    simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22928 (p : Pattern) (guard : d180017 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180016 p = 1 := by simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22927 p hg
    simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22929 (p : Pattern) (guard : d180018 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180017 p = 1 := by simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22928 p hg
    simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22930 (p : Pattern) (guard : d180019 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180018 p = 1 := by simpa only [d180019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22929 p hg
    simpa only [d180019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22931 (p : Pattern) (guard : d180020 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180015 p = 1 := by simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22926 p hg
    simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22932 (p : Pattern) (guard : d180021 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180020 p = 1 := by simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22931 p hg
    simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22933 (p : Pattern) (guard : d180022 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180021 p = 1 := by simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22932 p hg
    simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22934 (p : Pattern) (guard : d180023 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180022 p = 1 := by simpa only [d180023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22933 p hg
    simpa only [d180023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22935 (p : Pattern) (guard : d180024 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180019 p = 1 := by simpa only [d180024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22930 p hg
    simpa only [d180024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180023 p = 1 := by simpa only [d180024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22934 p hg
    simpa only [d180024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22936 (p : Pattern) (guard : d180025 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180024 p = 1 := by simpa only [d180025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22935 p hg
    simpa only [d180025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22937 (p : Pattern) (guard : d180026 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180025 p = 1 := by simpa only [d180026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22936 p hg
    simpa only [d180026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22938 (p : Pattern) (guard : d180027 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180026 p = 1 := by simpa only [d180027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22937 p hg
    simpa only [d180027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22939 (p : Pattern) (guard : d180028 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180027 p = 1 := by simpa only [d180028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22938 p hg
    simpa only [d180028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22940 (p : Pattern) (guard : d180032 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180018 p = 1 := by simpa only [d180032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22901 p hg
    simpa only [d180032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22941 (p : Pattern) (guard : d180033 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180022 p = 1 := by simpa only [d180033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22905 p hg
    simpa only [d180033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22942 (p : Pattern) (guard : d180034 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180032 p = 1 := by simpa only [d180034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22940 p hg
    simpa only [d180034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180033 p = 1 := by simpa only [d180034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22941 p hg
    simpa only [d180034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22943 (p : Pattern) (guard : d180035 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180034 p = 1 := by simpa only [d180035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22942 p hg
    simpa only [d180035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22944 (p : Pattern) (guard : d180036 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180035 p = 1 := by simpa only [d180036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22943 p hg
    simpa only [d180036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22945 (p : Pattern) (guard : d180037 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180036 p = 1 := by simpa only [d180037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22944 p hg
    simpa only [d180037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22946 (p : Pattern) (guard : d180038 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180037 p = 1 := by simpa only [d180038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22945 p hg
    simpa only [d180038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22947 (p : Pattern) (guard : d180039 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d180028 p = 1 := by simpa only [d180039, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22939 p hg
    simpa only [d180039, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180038 p = 1 := by simpa only [d180039, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22946 p hg
    simpa only [d180039, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22948 (p : Pattern) (guard : d180040 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d180029 p = 1 := by simpa only [d180040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22912 p hg
    simpa only [d180040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180039 p = 1 := by simpa only [d180040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22947 p hg
    simpa only [d180040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22949 (p : Pattern) (guard : d180041 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180040 p = 1 := by simpa only [d180041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22948 p hg
    simpa only [d180041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d180041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22950 (p : Pattern) (guard : d180042 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180031 p = 1 := by simpa only [d180042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22914 p hg
    simpa only [d180042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180041 p = 1 := by simpa only [d180042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22949 p hg
    simpa only [d180042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22951 (p : Pattern) (guard : d180043 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180017 p = 1 := by simpa only [d180043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22900 p hg
    simpa only [d180043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22952 (p : Pattern) (guard : d180044 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180043 p = 1 := by simpa only [d180044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22951 p hg
    simpa only [d180044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22953 (p : Pattern) (guard : d180045 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180021 p = 1 := by simpa only [d180045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22904 p hg
    simpa only [d180045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22954 (p : Pattern) (guard : d180046 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180045 p = 1 := by simpa only [d180046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22953 p hg
    simpa only [d180046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22955 (p : Pattern) (guard : d180047 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180044 p = 1 := by simpa only [d180047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22952 p hg
    simpa only [d180047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180046 p = 1 := by simpa only [d180047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22954 p hg
    simpa only [d180047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22956 (p : Pattern) (guard : d180048 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180047 p = 1 := by simpa only [d180048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22955 p hg
    simpa only [d180048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22957 (p : Pattern) (guard : d180049 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180048 p = 1 := by simpa only [d180049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22956 p hg
    simpa only [d180049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22958 (p : Pattern) (guard : d180050 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180049 p = 1 := by simpa only [d180050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22957 p hg
    simpa only [d180050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22959 (p : Pattern) (guard : d180051 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180016 p = 1 := by simpa only [d180051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22899 p hg
    simpa only [d180051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22960 (p : Pattern) (guard : d180052 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180051 p = 1 := by simpa only [d180052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22959 p hg
    simpa only [d180052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22961 (p : Pattern) (guard : d180053 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180052 p = 1 := by simpa only [d180053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22960 p hg
    simpa only [d180053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22962 (p : Pattern) (guard : d180054 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180020 p = 1 := by simpa only [d180054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22903 p hg
    simpa only [d180054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22963 (p : Pattern) (guard : d180055 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180054 p = 1 := by simpa only [d180055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22962 p hg
    simpa only [d180055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22964 (p : Pattern) (guard : d180056 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180055 p = 1 := by simpa only [d180056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22963 p hg
    simpa only [d180056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22965 (p : Pattern) (guard : d180057 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180053 p = 1 := by simpa only [d180057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22961 p hg
    simpa only [d180057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180056 p = 1 := by simpa only [d180057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22964 p hg
    simpa only [d180057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22966 (p : Pattern) (guard : d180058 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180057 p = 1 := by simpa only [d180058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22965 p hg
    simpa only [d180058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22967 (p : Pattern) (guard : d180059 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180058 p = 1 := by simpa only [d180059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22966 p hg
    simpa only [d180059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22968 (p : Pattern) (guard : d17226 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17225 p = 1 := by simpa only [d17226, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16058 p hg
    simpa only [d17226, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17226, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21624 p hg
    simpa only [d17226, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22969 (p : Pattern) (guard : d22767 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d22767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d22767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17226 p = 1 := by simpa only [d22767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22968 p hg
    simpa only [d22767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22970 (p : Pattern) (guard : d149593 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d22767 p = 1 := by simpa only [d149593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22969 p hg
    simpa only [d149593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d149593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d149593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22971 (p : Pattern) (guard : d180060 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d149593 p = 1 := by simpa only [d180060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22970 p hg
    simpa only [d180060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179989 p = 1 := by simpa only [d180060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22878 p hg
    simpa only [d180060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22972 (p : Pattern) (guard : d180061 p = 1) : d48326 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180061, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d180061, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180060 p = 1 := by simpa only [d180061, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22971 p hg
    simpa only [d180061, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22973 (p : Pattern) (guard : d180062 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180062, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d180062, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180061 p = 1 := by simpa only [d180062, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22972 p hg
    simpa only [d180062, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22974 (p : Pattern) (guard : d180063 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179989 p = 1 := by simpa only [d180063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22878 p hg
    simpa only [d180063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d180063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22975 (p : Pattern) (guard : d180064 p = 1) : d48326 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180064, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d180064, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180063 p = 1 := by simpa only [d180064, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22974 p hg
    simpa only [d180064, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22976 (p : Pattern) (guard : d180065 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180065, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d180065, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180064 p = 1 := by simpa only [d180065, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22975 p hg
    simpa only [d180065, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22977 (p : Pattern) (guard : d180066 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180062 p = 1 := by simpa only [d180066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22973 p hg
    simpa only [d180066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180065 p = 1 := by simpa only [d180066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22976 p hg
    simpa only [d180066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22978 (p : Pattern) (guard : d180067 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180066 p = 1 := by simpa only [d180067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22977 p hg
    simpa only [d180067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180006 p = 1 := by simpa only [d180067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22889 p hg
    simpa only [d180067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22979 (p : Pattern) (guard : d180068 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180067 p = 1 := by simpa only [d180068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22978 p hg
    simpa only [d180068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d180068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22980 (p : Pattern) (guard : d180069 p = 1) : d48338 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180068 p = 1 := by simpa only [d180069, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22979 p hg
    simpa only [d180069, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180069, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d180069, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22981 (p : Pattern) (guard : d180070 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180070, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d180070, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180069 p = 1 := by simpa only [d180070, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22980 p hg
    simpa only [d180070, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22982 (p : Pattern) (guard : d180071 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180070 p = 1 := by simpa only [d180071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22981 p hg
    simpa only [d180071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180011 p = 1 := by simpa only [d180071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22894 p hg
    simpa only [d180071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22983 (p : Pattern) (guard : d180072 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180071 p = 1 := by simpa only [d180072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22982 p hg
    simpa only [d180072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22984 (p : Pattern) (guard : d180073 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180072 p = 1 := by simpa only [d180073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22983 p hg
    simpa only [d180073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22985 (p : Pattern) (guard : d180074 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180073 p = 1 := by simpa only [d180074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22984 p hg
    simpa only [d180074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22986 (p : Pattern) (guard : d180075 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180074 p = 1 := by simpa only [d180075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22985 p hg
    simpa only [d180075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180019 p = 1 := by simpa only [d180075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22902 p hg
    simpa only [d180075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22987 (p : Pattern) (guard : d180076 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d180075 p = 1 := by simpa only [d180076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22986 p hg
    simpa only [d180076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22988 (p : Pattern) (guard : d180077 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180011 p = 1 := by simpa only [d180077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22894 p hg
    simpa only [d180077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22989 (p : Pattern) (guard : d180078 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180077 p = 1 := by simpa only [d180078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22988 p hg
    simpa only [d180078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22990 (p : Pattern) (guard : d180079 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180078 p = 1 := by simpa only [d180079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22989 p hg
    simpa only [d180079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22991 (p : Pattern) (guard : d180080 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180079 p = 1 := by simpa only [d180080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22990 p hg
    simpa only [d180080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22992 (p : Pattern) (guard : d180081 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180080 p = 1 := by simpa only [d180081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22991 p hg
    simpa only [d180081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22993 (p : Pattern) (guard : d180082 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d180081 p = 1 := by simpa only [d180082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22992 p hg
    simpa only [d180082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22994 (p : Pattern) (guard : d180083 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180076 p = 1 := by simpa only [d180083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22987 p hg
    simpa only [d180083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180082 p = 1 := by simpa only [d180083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22993 p hg
    simpa only [d180083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22995 (p : Pattern) (guard : d180084 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d180059 p = 1 := by simpa only [d180084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22967 p hg
    simpa only [d180084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180083 p = 1 := by simpa only [d180084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22994 p hg
    simpa only [d180084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22996 (p : Pattern) (guard : d180085 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d180050 p = 1 := by simpa only [d180085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22958 p hg
    simpa only [d180085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180084 p = 1 := by simpa only [d180085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22995 p hg
    simpa only [d180085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22997 (p : Pattern) (guard : d180086 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180086, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180086, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180085 p = 1 := by simpa only [d180086, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22996 p hg
    simpa only [d180086, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22998 (p : Pattern) (guard : d180043 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180017 p = 1 := by simpa only [d180043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22928 p hg
    simpa only [d180043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22999 (p : Pattern) (guard : d180044 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180043 p = 1 := by simpa only [d180044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22998 p hg
    simpa only [d180044, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
