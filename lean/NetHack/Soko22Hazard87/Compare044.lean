import NetHack.Soko22Hazard87.Compare043
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare11000 (p : Pattern) (guard : d159798 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d159797 p = 1 := by simpa only [d159798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10999 p hg
    simpa only [d159798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d159798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11001 (p : Pattern) (guard : d159799 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159799, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d159799, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159798 p = 1 := by simpa only [d159799, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11000 p hg
    simpa only [d159799, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11002 (p : Pattern) (guard : d159800 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159800, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d159800, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159799 p = 1 := by simpa only [d159800, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11001 p hg
    simpa only [d159800, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11003 (p : Pattern) (guard : d0 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11004 (p : Pattern) (guard : d159801 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d159800 p = 1 := by simpa only [d159801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11002 p hg
    simpa only [d159801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d159801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11005 (p : Pattern) (guard : d159802 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d159801 p = 1 := by simpa only [d159802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11004 p hg
    simpa only [d159802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d159802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11006 (p : Pattern) (guard : d159803 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d159802 p = 1 := by simpa only [d159803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11005 p hg
    simpa only [d159803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d159803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11007 (p : Pattern) (guard : d0 p = 1) : d47698 p ≤ (-1 : Int) + d159768 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11008 (p : Pattern) (guard : d159804 p = 1) : d47699 p ≤ (-1 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d159803 p = 1 := by simpa only [d159804, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11006 p hg
    simpa only [d159804, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159804, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d159804, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11009 (p : Pattern) (guard : d159805 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159805, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d159805, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159804 p = 1 := by simpa only [d159805, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11008 p hg
    simpa only [d159805, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11010 (p : Pattern) (guard : d159806 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d159805 p = 1 := by simpa only [d159806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11009 p hg
    simpa only [d159806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11011 (p : Pattern) (guard : d159807 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d159806 p = 1 := by simpa only [d159807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11010 p hg
    simpa only [d159807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11012 (p : Pattern) (guard : d159808 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d159807 p = 1 := by simpa only [d159808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11011 p hg
    simpa only [d159808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11013 (p : Pattern) (guard : d159809 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159808 p = 1 := by simpa only [d159809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11012 p hg
    simpa only [d159809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11014 (p : Pattern) (guard : d159810 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159809 p = 1 := by simpa only [d159810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11013 p hg
    simpa only [d159810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11015 (p : Pattern) (guard : d159811 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d159810 p = 1 := by simpa only [d159811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11014 p hg
    simpa only [d159811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11016 (p : Pattern) (guard : d159812 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159811 p = 1 := by simpa only [d159812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11015 p hg
    simpa only [d159812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11017 (p : Pattern) (guard : d159813 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159812 p = 1 := by simpa only [d159813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11016 p hg
    simpa only [d159813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11018 (p : Pattern) (guard : d159814 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159813 p = 1 := by simpa only [d159814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11017 p hg
    simpa only [d159814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11019 (p : Pattern) (guard : d159815 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159814 p = 1 := by simpa only [d159815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11018 p hg
    simpa only [d159815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11020 (p : Pattern) (guard : d159816 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d159808 p = 1 := by simpa only [d159816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11012 p hg
    simpa only [d159816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11021 (p : Pattern) (guard : d159817 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159816 p = 1 := by simpa only [d159817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11020 p hg
    simpa only [d159817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11022 (p : Pattern) (guard : d159818 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d159817 p = 1 := by simpa only [d159818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11021 p hg
    simpa only [d159818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11023 (p : Pattern) (guard : d159819 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159818 p = 1 := by simpa only [d159819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11022 p hg
    simpa only [d159819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11024 (p : Pattern) (guard : d159820 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159819 p = 1 := by simpa only [d159820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11023 p hg
    simpa only [d159820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11025 (p : Pattern) (guard : d159821 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159820 p = 1 := by simpa only [d159821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11024 p hg
    simpa only [d159821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11026 (p : Pattern) (guard : d159822 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d159814 p = 1 := by simpa only [d159822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11018 p hg
    simpa only [d159822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159821 p = 1 := by simpa only [d159822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11025 p hg
    simpa only [d159822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11027 (p : Pattern) (guard : d159823 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d159815 p = 1 := by simpa only [d159823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11019 p hg
    simpa only [d159823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159822 p = 1 := by simpa only [d159823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11026 p hg
    simpa only [d159823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11028 (p : Pattern) (guard : d159824 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d159823 p = 1 := by simpa only [d159824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11027 p hg
    simpa only [d159824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11029 (p : Pattern) (guard : d159825 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d159824 p = 1 := by simpa only [d159825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11028 p hg
    simpa only [d159825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11030 (p : Pattern) (guard : d159826 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159825 p = 1 := by simpa only [d159826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11029 p hg
    simpa only [d159826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11031 (p : Pattern) (guard : d0 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11032 (p : Pattern) (guard : d0 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11033 (p : Pattern) (guard : d0 p = 1) : d47763 p ≤ (-1 : Int) + d159774 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11034 (p : Pattern) (guard : d0 p = 1) : d47746 p ≤ (-1 : Int) + d100911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11035 (p : Pattern) (guard : d0 p = 1) : d47751 p ≤ (-1 : Int) + d47750 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11036 (p : Pattern) (guard : d0 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11037 (p : Pattern) (guard : d0 p = 1) : d47734 p ≤ (-1 : Int) + d47753 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11038 (p : Pattern) (guard : d27 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d27, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4483 p hg
    simpa only [d27, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11039 (p : Pattern) (guard : d0 p = 1) : d47754 p ≤ (-1 : Int) + d47754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11040 (p : Pattern) (guard : d28 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11038 p hg
    simpa only [d28, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d28, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11041 (p : Pattern) (guard : d159796 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d159796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d159796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11040 p hg
    simpa only [d159796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11042 (p : Pattern) (guard : d159797 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d159796 p = 1 := by simpa only [d159797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11041 p hg
    simpa only [d159797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d159797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11043 (p : Pattern) (guard : d159798 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d159797 p = 1 := by simpa only [d159798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11042 p hg
    simpa only [d159798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d159798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11044 (p : Pattern) (guard : d159799 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159799, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d159799, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159798 p = 1 := by simpa only [d159799, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11043 p hg
    simpa only [d159799, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11045 (p : Pattern) (guard : d159800 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159800, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d159800, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159799 p = 1 := by simpa only [d159800, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11044 p hg
    simpa only [d159800, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11046 (p : Pattern) (guard : d0 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11047 (p : Pattern) (guard : d159801 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d159800 p = 1 := by simpa only [d159801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11045 p hg
    simpa only [d159801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d159801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11048 (p : Pattern) (guard : d159802 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d159801 p = 1 := by simpa only [d159802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11047 p hg
    simpa only [d159802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d159802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11049 (p : Pattern) (guard : d159803 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d159802 p = 1 := by simpa only [d159803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11048 p hg
    simpa only [d159803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d159803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11050 (p : Pattern) (guard : d0 p = 1) : d47764 p ≤ (-1 : Int) + d159773 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11051 (p : Pattern) (guard : d159804 p = 1) : d47765 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d159803 p = 1 := by simpa only [d159804, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11049 p hg
    simpa only [d159804, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159804, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d159804, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11052 (p : Pattern) (guard : d159805 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159805, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d159805, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159804 p = 1 := by simpa only [d159805, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11051 p hg
    simpa only [d159805, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11053 (p : Pattern) (guard : d159806 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d159805 p = 1 := by simpa only [d159806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11052 p hg
    simpa only [d159806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11054 (p : Pattern) (guard : d159807 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d159806 p = 1 := by simpa only [d159807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11053 p hg
    simpa only [d159807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11055 (p : Pattern) (guard : d159808 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d159807 p = 1 := by simpa only [d159808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11054 p hg
    simpa only [d159808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11056 (p : Pattern) (guard : d159816 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d159808 p = 1 := by simpa only [d159816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11055 p hg
    simpa only [d159816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11057 (p : Pattern) (guard : d159817 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159816 p = 1 := by simpa only [d159817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11056 p hg
    simpa only [d159817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11058 (p : Pattern) (guard : d159818 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d159817 p = 1 := by simpa only [d159818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11057 p hg
    simpa only [d159818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11059 (p : Pattern) (guard : d159819 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159818 p = 1 := by simpa only [d159819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11058 p hg
    simpa only [d159819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11060 (p : Pattern) (guard : d159820 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159819 p = 1 := by simpa only [d159820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11059 p hg
    simpa only [d159820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11061 (p : Pattern) (guard : d159821 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159820 p = 1 := by simpa only [d159821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11060 p hg
    simpa only [d159821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11062 (p : Pattern) (guard : d159827 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159827, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159827, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159821 p = 1 := by simpa only [d159827, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11061 p hg
    simpa only [d159827, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11063 (p : Pattern) (guard : d159828 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d159828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159827 p = 1 := by simpa only [d159828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11062 p hg
    simpa only [d159828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11064 (p : Pattern) (guard : d159829 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 69 with
  | false =>
    have hg : d159828 p = 1 := by simpa only [d159829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11063 p hg
    simpa only [d159829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d159829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11065 (p : Pattern) (guard : d159830 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 51 with
  | false =>
    have hg : d159829 p = 1 := by simpa only [d159830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11064 p hg
    simpa only [d159830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d159830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11066 (p : Pattern) (guard : d159831 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 50 with
  | false =>
    have hg : d159830 p = 1 := by simpa only [d159831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11065 p hg
    simpa only [d159831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d159831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11067 (p : Pattern) (guard : d159832 p = 1) : d47768 p ≤ (-1 : Int) + d159776 p := by
  cases selected : p 49 with
  | false =>
    have hg : d159826 p = 1 := by simpa only [d159832, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11030 p hg
    simpa only [d159832, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159831 p = 1 := by simpa only [d159832, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11066 p hg
    simpa only [d159832, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11068 (p : Pattern) (guard : d0 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11069 (p : Pattern) (guard : d0 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11070 (p : Pattern) (guard : d0 p = 1) : d47786 p ≤ (-1 : Int) + d159777 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11071 (p : Pattern) (guard : d0 p = 1) : d47796 p ≤ (-1 : Int) + d47795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11072 (p : Pattern) (guard : d0 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11073 (p : Pattern) (guard : d0 p = 1) : d47652 p ≤ (-1 : Int) + d47792 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11074 (p : Pattern) (guard : d66 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d66, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d24 p = 1 := by simpa only [d66, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4534 p hg
    simpa only [d66, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11075 (p : Pattern) (guard : d67 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d66 p = 1 := by simpa only [d67, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11074 p hg
    simpa only [d67, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25 p = 1 := by simpa only [d67, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4536 p hg
    simpa only [d67, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11076 (p : Pattern) (guard : d68 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d67 p = 1 := by simpa only [d68, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11075 p hg
    simpa only [d68, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d68, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4554 p hg
    simpa only [d68, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11077 (p : Pattern) (guard : d0 p = 1) : d47802 p ≤ (-1 : Int) + d47802 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11078 (p : Pattern) (guard : d69 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d68 p = 1 := by simpa only [d69, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11076 p hg
    simpa only [d69, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d69, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d69, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11079 (p : Pattern) (guard : d159833 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d159833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d69 p = 1 := by simpa only [d159833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11078 p hg
    simpa only [d159833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11080 (p : Pattern) (guard : d159834 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d159833 p = 1 := by simpa only [d159834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11079 p hg
    simpa only [d159834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d159834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11081 (p : Pattern) (guard : d159835 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d159834 p = 1 := by simpa only [d159835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11080 p hg
    simpa only [d159835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d159835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11082 (p : Pattern) (guard : d159836 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159836, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d159836, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159835 p = 1 := by simpa only [d159836, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11081 p hg
    simpa only [d159836, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11083 (p : Pattern) (guard : d159837 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159837, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d159837, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159836 p = 1 := by simpa only [d159837, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11082 p hg
    simpa only [d159837, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11084 (p : Pattern) (guard : d0 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11085 (p : Pattern) (guard : d159838 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d159837 p = 1 := by simpa only [d159838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11083 p hg
    simpa only [d159838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d159838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11086 (p : Pattern) (guard : d159839 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d159838 p = 1 := by simpa only [d159839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11085 p hg
    simpa only [d159839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d159839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11087 (p : Pattern) (guard : d159840 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d159839 p = 1 := by simpa only [d159840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11086 p hg
    simpa only [d159840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d159840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11088 (p : Pattern) (guard : d0 p = 1) : d47806 p ≤ (-1 : Int) + d159780 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11089 (p : Pattern) (guard : d159841 p = 1) : d47807 p ≤ (-1 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d159840 p = 1 := by simpa only [d159841, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11087 p hg
    simpa only [d159841, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159841, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d159841, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11090 (p : Pattern) (guard : d159842 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159842, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d159842, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159841 p = 1 := by simpa only [d159842, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11089 p hg
    simpa only [d159842, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11091 (p : Pattern) (guard : d159843 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d159842 p = 1 := by simpa only [d159843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11090 p hg
    simpa only [d159843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d159843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11092 (p : Pattern) (guard : d159844 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d159843 p = 1 := by simpa only [d159844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11091 p hg
    simpa only [d159844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d159844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11093 (p : Pattern) (guard : d159845 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d159844 p = 1 := by simpa only [d159845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11092 p hg
    simpa only [d159845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d159845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11094 (p : Pattern) (guard : d159846 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d159845 p = 1 := by simpa only [d159846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11093 p hg
    simpa only [d159846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d159846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11095 (p : Pattern) (guard : d159847 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159846 p = 1 := by simpa only [d159847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11094 p hg
    simpa only [d159847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d159847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11096 (p : Pattern) (guard : d159848 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d159847 p = 1 := by simpa only [d159848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11095 p hg
    simpa only [d159848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d159848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11097 (p : Pattern) (guard : d159849 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159848 p = 1 := by simpa only [d159849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11096 p hg
    simpa only [d159849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d159849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11098 (p : Pattern) (guard : d159850 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d159850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159849 p = 1 := by simpa only [d159850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11097 p hg
    simpa only [d159850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11099 (p : Pattern) (guard : d159851 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d159851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159850 p = 1 := by simpa only [d159851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11098 p hg
    simpa only [d159851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11100 (p : Pattern) (guard : d159852 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159852, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159852, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159851 p = 1 := by simpa only [d159852, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11099 p hg
    simpa only [d159852, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11101 (p : Pattern) (guard : d159853 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d159853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159852 p = 1 := by simpa only [d159853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11100 p hg
    simpa only [d159853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11102 (p : Pattern) (guard : d159854 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 69 with
  | false =>
    have hg : d159853 p = 1 := by simpa only [d159854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11101 p hg
    simpa only [d159854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d159854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11103 (p : Pattern) (guard : d159855 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 51 with
  | false =>
    have hg : d159854 p = 1 := by simpa only [d159855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11102 p hg
    simpa only [d159855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d159855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11104 (p : Pattern) (guard : d159856 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 50 with
  | false =>
    have hg : d159855 p = 1 := by simpa only [d159856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11103 p hg
    simpa only [d159856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d159856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11105 (p : Pattern) (guard : d0 p = 1) : d47864 p ≤ (-1 : Int) + d159793 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11106 (p : Pattern) (guard : d159857 p = 1) : d47865 p ≤ (-1 : Int) + d159794 p := by
  cases selected : p 49 with
  | false =>
    have hg : d159856 p = 1 := by simpa only [d159857, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11104 p hg
    simpa only [d159857, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159857, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11105 p hg
    simpa only [d159857, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11107 (p : Pattern) (guard : d159858 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 48 with
  | false =>
    have hg : d159832 p = 1 := by simpa only [d159858, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11067 p hg
    simpa only [d159858, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159857 p = 1 := by simpa only [d159858, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11106 p hg
    simpa only [d159858, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11108 (p : Pattern) (guard : d159859 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d159859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159858 p = 1 := by simpa only [d159859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11107 p hg
    simpa only [d159859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11109 (p : Pattern) (guard : d159860 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d159860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159859 p = 1 := by simpa only [d159860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11108 p hg
    simpa only [d159860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11110 (p : Pattern) (guard : d159861 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d159861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159860 p = 1 := by simpa only [d159861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11109 p hg
    simpa only [d159861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11111 (p : Pattern) (guard : d159862 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d159862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159861 p = 1 := by simpa only [d159862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11110 p hg
    simpa only [d159862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11112 (p : Pattern) (guard : d159863 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d159863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159862 p = 1 := by simpa only [d159863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11111 p hg
    simpa only [d159863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11113 (p : Pattern) (guard : d159864 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159810 p = 1 := by simpa only [d159864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11014 p hg
    simpa only [d159864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11114 (p : Pattern) (guard : d159865 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159864 p = 1 := by simpa only [d159865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11113 p hg
    simpa only [d159865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11115 (p : Pattern) (guard : d159866 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159865 p = 1 := by simpa only [d159866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11114 p hg
    simpa only [d159866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11116 (p : Pattern) (guard : d159867 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159866 p = 1 := by simpa only [d159867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11115 p hg
    simpa only [d159867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11117 (p : Pattern) (guard : d159868 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159867 p = 1 := by simpa only [d159868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11116 p hg
    simpa only [d159868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11118 (p : Pattern) (guard : d159869 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159868 p = 1 := by simpa only [d159869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11117 p hg
    simpa only [d159869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11119 (p : Pattern) (guard : d159870 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d159869 p = 1 := by simpa only [d159870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11118 p hg
    simpa only [d159870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11120 (p : Pattern) (guard : d159871 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159817 p = 1 := by simpa only [d159871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11021 p hg
    simpa only [d159871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11121 (p : Pattern) (guard : d159872 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159871 p = 1 := by simpa only [d159872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11120 p hg
    simpa only [d159872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11122 (p : Pattern) (guard : d159873 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159872 p = 1 := by simpa only [d159873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11121 p hg
    simpa only [d159873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11123 (p : Pattern) (guard : d159874 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159873 p = 1 := by simpa only [d159874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11122 p hg
    simpa only [d159874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11124 (p : Pattern) (guard : d159875 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d159867 p = 1 := by simpa only [d159875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11116 p hg
    simpa only [d159875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159874 p = 1 := by simpa only [d159875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11123 p hg
    simpa only [d159875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11125 (p : Pattern) (guard : d159876 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d159868 p = 1 := by simpa only [d159876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11117 p hg
    simpa only [d159876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159875 p = 1 := by simpa only [d159876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11124 p hg
    simpa only [d159876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11126 (p : Pattern) (guard : d159877 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d159876 p = 1 := by simpa only [d159877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11125 p hg
    simpa only [d159877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11127 (p : Pattern) (guard : d159878 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d159870 p = 1 := by simpa only [d159878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11119 p hg
    simpa only [d159878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159877 p = 1 := by simpa only [d159878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11126 p hg
    simpa only [d159878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11128 (p : Pattern) (guard : d159879 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159807 p = 1 := by simpa only [d159879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11011 p hg
    simpa only [d159879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11129 (p : Pattern) (guard : d159880 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159879 p = 1 := by simpa only [d159880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11128 p hg
    simpa only [d159880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11130 (p : Pattern) (guard : d159881 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159880 p = 1 := by simpa only [d159881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11129 p hg
    simpa only [d159881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11131 (p : Pattern) (guard : d159882 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159881 p = 1 := by simpa only [d159882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11130 p hg
    simpa only [d159882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11132 (p : Pattern) (guard : d159883 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159882 p = 1 := by simpa only [d159883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11131 p hg
    simpa only [d159883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11133 (p : Pattern) (guard : d159884 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159883 p = 1 := by simpa only [d159884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11132 p hg
    simpa only [d159884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11134 (p : Pattern) (guard : d159885 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159806 p = 1 := by simpa only [d159885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11010 p hg
    simpa only [d159885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11135 (p : Pattern) (guard : d159886 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d159885 p = 1 := by simpa only [d159886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11134 p hg
    simpa only [d159886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11136 (p : Pattern) (guard : d159887 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159886 p = 1 := by simpa only [d159887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11135 p hg
    simpa only [d159887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11137 (p : Pattern) (guard : d159888 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159887 p = 1 := by simpa only [d159888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11136 p hg
    simpa only [d159888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11138 (p : Pattern) (guard : d159889 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159888 p = 1 := by simpa only [d159889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11137 p hg
    simpa only [d159889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11139 (p : Pattern) (guard : d159890 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159889 p = 1 := by simpa only [d159890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11138 p hg
    simpa only [d159890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11140 (p : Pattern) (guard : d141 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d141, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d141, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d141, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4633 p hg
    simpa only [d141, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11141 (p : Pattern) (guard : d142 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11140 p hg
    simpa only [d142, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d142, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11142 (p : Pattern) (guard : d159891 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d159891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d159891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11141 p hg
    simpa only [d159891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11143 (p : Pattern) (guard : d159892 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d159891 p = 1 := by simpa only [d159892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11142 p hg
    simpa only [d159892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d159892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11144 (p : Pattern) (guard : d159893 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d159892 p = 1 := by simpa only [d159893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11143 p hg
    simpa only [d159893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159797 p = 1 := by simpa only [d159893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10999 p hg
    simpa only [d159893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11145 (p : Pattern) (guard : d159894 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159894, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d159894, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159893 p = 1 := by simpa only [d159894, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11144 p hg
    simpa only [d159894, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11146 (p : Pattern) (guard : d159895 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159895, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d159895, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159894 p = 1 := by simpa only [d159895, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11145 p hg
    simpa only [d159895, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11147 (p : Pattern) (guard : d159896 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d159895 p = 1 := by simpa only [d159896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11146 p hg
    simpa only [d159896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159800 p = 1 := by simpa only [d159896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11002 p hg
    simpa only [d159896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11148 (p : Pattern) (guard : d159897 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d159896 p = 1 := by simpa only [d159897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11147 p hg
    simpa only [d159897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159801 p = 1 := by simpa only [d159897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11004 p hg
    simpa only [d159897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11149 (p : Pattern) (guard : d159898 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d159897 p = 1 := by simpa only [d159898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11148 p hg
    simpa only [d159898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d159898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11150 (p : Pattern) (guard : d159899 p = 1) : d47699 p ≤ (-1 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d159898 p = 1 := by simpa only [d159899, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11149 p hg
    simpa only [d159899, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159899, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d159899, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11151 (p : Pattern) (guard : d159900 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159900, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d159900, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159899 p = 1 := by simpa only [d159900, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11150 p hg
    simpa only [d159900, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11152 (p : Pattern) (guard : d159901 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d159900 p = 1 := by simpa only [d159901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11151 p hg
    simpa only [d159901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159805 p = 1 := by simpa only [d159901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11009 p hg
    simpa only [d159901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11153 (p : Pattern) (guard : d159902 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d159901 p = 1 := by simpa only [d159902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11152 p hg
    simpa only [d159902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11154 (p : Pattern) (guard : d159903 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d159902 p = 1 := by simpa only [d159903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11153 p hg
    simpa only [d159903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11155 (p : Pattern) (guard : d159904 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159903 p = 1 := by simpa only [d159904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11154 p hg
    simpa only [d159904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11156 (p : Pattern) (guard : d159905 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159904 p = 1 := by simpa only [d159905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11155 p hg
    simpa only [d159905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159809 p = 1 := by simpa only [d159905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11013 p hg
    simpa only [d159905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11157 (p : Pattern) (guard : d159906 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d159905 p = 1 := by simpa only [d159906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11156 p hg
    simpa only [d159906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11158 (p : Pattern) (guard : d159907 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159906 p = 1 := by simpa only [d159907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11157 p hg
    simpa only [d159907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159811 p = 1 := by simpa only [d159907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11015 p hg
    simpa only [d159907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11159 (p : Pattern) (guard : d159908 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d159890 p = 1 := by simpa only [d159908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11139 p hg
    simpa only [d159908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159907 p = 1 := by simpa only [d159908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11158 p hg
    simpa only [d159908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11160 (p : Pattern) (guard : d159909 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d159884 p = 1 := by simpa only [d159909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11133 p hg
    simpa only [d159909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159908 p = 1 := by simpa only [d159909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11159 p hg
    simpa only [d159909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11161 (p : Pattern) (guard : d159910 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159909 p = 1 := by simpa only [d159910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11160 p hg
    simpa only [d159910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11162 (p : Pattern) (guard : d159911 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d159879 p = 1 := by simpa only [d159911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11128 p hg
    simpa only [d159911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11163 (p : Pattern) (guard : d159912 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159911 p = 1 := by simpa only [d159912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11162 p hg
    simpa only [d159912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11164 (p : Pattern) (guard : d159913 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159912 p = 1 := by simpa only [d159913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11163 p hg
    simpa only [d159913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11165 (p : Pattern) (guard : d159914 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159913 p = 1 := by simpa only [d159914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11164 p hg
    simpa only [d159914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11166 (p : Pattern) (guard : d159915 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159914 p = 1 := by simpa only [d159915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11165 p hg
    simpa only [d159915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11167 (p : Pattern) (guard : d159916 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d159886 p = 1 := by simpa only [d159916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11135 p hg
    simpa only [d159916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11168 (p : Pattern) (guard : d159917 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159916 p = 1 := by simpa only [d159917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11167 p hg
    simpa only [d159917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11169 (p : Pattern) (guard : d159918 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159917 p = 1 := by simpa only [d159918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11168 p hg
    simpa only [d159918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11170 (p : Pattern) (guard : d159919 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159918 p = 1 := by simpa only [d159919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11169 p hg
    simpa only [d159919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11171 (p : Pattern) (guard : d159920 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d159903 p = 1 := by simpa only [d159920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11154 p hg
    simpa only [d159920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11172 (p : Pattern) (guard : d159921 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159920 p = 1 := by simpa only [d159921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11171 p hg
    simpa only [d159921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159816 p = 1 := by simpa only [d159921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11020 p hg
    simpa only [d159921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11173 (p : Pattern) (guard : d159922 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d159921 p = 1 := by simpa only [d159922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11172 p hg
    simpa only [d159922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11174 (p : Pattern) (guard : d159923 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159922 p = 1 := by simpa only [d159923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11173 p hg
    simpa only [d159923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159818 p = 1 := by simpa only [d159923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11022 p hg
    simpa only [d159923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11175 (p : Pattern) (guard : d159924 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d159919 p = 1 := by simpa only [d159924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11170 p hg
    simpa only [d159924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159923 p = 1 := by simpa only [d159924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11174 p hg
    simpa only [d159924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11176 (p : Pattern) (guard : d159925 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d159915 p = 1 := by simpa only [d159925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11166 p hg
    simpa only [d159925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159924 p = 1 := by simpa only [d159925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11175 p hg
    simpa only [d159925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11177 (p : Pattern) (guard : d159926 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d159909 p = 1 := by simpa only [d159926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11160 p hg
    simpa only [d159926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159925 p = 1 := by simpa only [d159926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11176 p hg
    simpa only [d159926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11178 (p : Pattern) (guard : d159927 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d159910 p = 1 := by simpa only [d159927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11161 p hg
    simpa only [d159927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159926 p = 1 := by simpa only [d159927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11177 p hg
    simpa only [d159927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11179 (p : Pattern) (guard : d159928 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d159867 p = 1 := by simpa only [d159928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11116 p hg
    simpa only [d159928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11180 (p : Pattern) (guard : d159929 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d159928 p = 1 := by simpa only [d159929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11179 p hg
    simpa only [d159929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11181 (p : Pattern) (guard : d159930 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d159927 p = 1 := by simpa only [d159930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11178 p hg
    simpa only [d159930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159929 p = 1 := by simpa only [d159930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11180 p hg
    simpa only [d159930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11182 (p : Pattern) (guard : d159931 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d159930 p = 1 := by simpa only [d159931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11181 p hg
    simpa only [d159931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11183 (p : Pattern) (guard : d159932 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 50 with
  | false =>
    have hg : d159878 p = 1 := by simpa only [d159932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11127 p hg
    simpa only [d159932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159931 p = 1 := by simpa only [d159932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11182 p hg
    simpa only [d159932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11184 (p : Pattern) (guard : d141 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d141, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d141, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d141, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4692 p hg
    simpa only [d141, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11185 (p : Pattern) (guard : d142 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11184 p hg
    simpa only [d142, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d142, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11186 (p : Pattern) (guard : d159891 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d159891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d159891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11185 p hg
    simpa only [d159891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11187 (p : Pattern) (guard : d159892 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d159891 p = 1 := by simpa only [d159892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11186 p hg
    simpa only [d159892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d159892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11188 (p : Pattern) (guard : d159893 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d159892 p = 1 := by simpa only [d159893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11187 p hg
    simpa only [d159893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159797 p = 1 := by simpa only [d159893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11042 p hg
    simpa only [d159893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11189 (p : Pattern) (guard : d159894 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159894, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d159894, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159893 p = 1 := by simpa only [d159894, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11188 p hg
    simpa only [d159894, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11190 (p : Pattern) (guard : d159895 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159895, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d159895, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159894 p = 1 := by simpa only [d159895, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11189 p hg
    simpa only [d159895, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11191 (p : Pattern) (guard : d159896 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d159895 p = 1 := by simpa only [d159896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11190 p hg
    simpa only [d159896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159800 p = 1 := by simpa only [d159896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11045 p hg
    simpa only [d159896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11192 (p : Pattern) (guard : d159897 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d159896 p = 1 := by simpa only [d159897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11191 p hg
    simpa only [d159897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159801 p = 1 := by simpa only [d159897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11047 p hg
    simpa only [d159897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11193 (p : Pattern) (guard : d159898 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d159897 p = 1 := by simpa only [d159898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11192 p hg
    simpa only [d159898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d159898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11194 (p : Pattern) (guard : d159899 p = 1) : d47765 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d159898 p = 1 := by simpa only [d159899, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11193 p hg
    simpa only [d159899, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159899, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d159899, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11195 (p : Pattern) (guard : d159900 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159900, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d159900, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159899 p = 1 := by simpa only [d159900, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11194 p hg
    simpa only [d159900, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11196 (p : Pattern) (guard : d159901 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d159900 p = 1 := by simpa only [d159901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11195 p hg
    simpa only [d159901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159805 p = 1 := by simpa only [d159901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11052 p hg
    simpa only [d159901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11197 (p : Pattern) (guard : d159902 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d159901 p = 1 := by simpa only [d159902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11196 p hg
    simpa only [d159902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11198 (p : Pattern) (guard : d159903 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d159902 p = 1 := by simpa only [d159903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11197 p hg
    simpa only [d159903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11199 (p : Pattern) (guard : d159920 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d159903 p = 1 := by simpa only [d159920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11198 p hg
    simpa only [d159920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11200 (p : Pattern) (guard : d159921 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159920 p = 1 := by simpa only [d159921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11199 p hg
    simpa only [d159921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159816 p = 1 := by simpa only [d159921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11056 p hg
    simpa only [d159921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11201 (p : Pattern) (guard : d159922 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d159921 p = 1 := by simpa only [d159922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11200 p hg
    simpa only [d159922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11202 (p : Pattern) (guard : d159923 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159922 p = 1 := by simpa only [d159923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11201 p hg
    simpa only [d159923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159818 p = 1 := by simpa only [d159923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11058 p hg
    simpa only [d159923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11203 (p : Pattern) (guard : d159933 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159923 p = 1 := by simpa only [d159933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11202 p hg
    simpa only [d159933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11204 (p : Pattern) (guard : d159934 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159933 p = 1 := by simpa only [d159934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11203 p hg
    simpa only [d159934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11205 (p : Pattern) (guard : d159935 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159935, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159935, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159934 p = 1 := by simpa only [d159935, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11204 p hg
    simpa only [d159935, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11206 (p : Pattern) (guard : d159936 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d159936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159935 p = 1 := by simpa only [d159936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11205 p hg
    simpa only [d159936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11207 (p : Pattern) (guard : d159937 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 69 with
  | false =>
    have hg : d159936 p = 1 := by simpa only [d159937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11206 p hg
    simpa only [d159937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d159937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11208 (p : Pattern) (guard : d159938 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 51 with
  | false =>
    have hg : d159937 p = 1 := by simpa only [d159938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11207 p hg
    simpa only [d159938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d159938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11209 (p : Pattern) (guard : d159939 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 50 with
  | false =>
    have hg : d159938 p = 1 := by simpa only [d159939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11208 p hg
    simpa only [d159939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d159939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11210 (p : Pattern) (guard : d159940 p = 1) : d47768 p ≤ (-1 : Int) + d159776 p := by
  cases selected : p 49 with
  | false =>
    have hg : d159932 p = 1 := by simpa only [d159940, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11183 p hg
    simpa only [d159940, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159939 p = 1 := by simpa only [d159940, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11209 p hg
    simpa only [d159940, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11211 (p : Pattern) (guard : d226 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d226, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d226, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d138 p = 1 := by simpa only [d226, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4732 p hg
    simpa only [d226, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11212 (p : Pattern) (guard : d227 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d226 p = 1 := by simpa only [d227, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11211 p hg
    simpa only [d227, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d139 p = 1 := by simpa only [d227, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4734 p hg
    simpa only [d227, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11213 (p : Pattern) (guard : d228 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d227 p = 1 := by simpa only [d228, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11212 p hg
    simpa only [d228, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d228, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4750 p hg
    simpa only [d228, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11214 (p : Pattern) (guard : d229 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d228 p = 1 := by simpa only [d229, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11213 p hg
    simpa only [d229, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d229, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d229, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11215 (p : Pattern) (guard : d159941 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d159941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d229 p = 1 := by simpa only [d159941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11214 p hg
    simpa only [d159941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11216 (p : Pattern) (guard : d159942 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d159941 p = 1 := by simpa only [d159942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11215 p hg
    simpa only [d159942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d159942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11217 (p : Pattern) (guard : d159943 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d159942 p = 1 := by simpa only [d159943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11216 p hg
    simpa only [d159943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159834 p = 1 := by simpa only [d159943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11080 p hg
    simpa only [d159943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11218 (p : Pattern) (guard : d159944 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159944, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d159944, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159943 p = 1 := by simpa only [d159944, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11217 p hg
    simpa only [d159944, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11219 (p : Pattern) (guard : d159945 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159945, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d159945, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159944 p = 1 := by simpa only [d159945, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11218 p hg
    simpa only [d159945, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11220 (p : Pattern) (guard : d159946 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d159945 p = 1 := by simpa only [d159946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11219 p hg
    simpa only [d159946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159837 p = 1 := by simpa only [d159946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11083 p hg
    simpa only [d159946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11221 (p : Pattern) (guard : d159947 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d159946 p = 1 := by simpa only [d159947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11220 p hg
    simpa only [d159947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159838 p = 1 := by simpa only [d159947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11085 p hg
    simpa only [d159947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11222 (p : Pattern) (guard : d159948 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d159947 p = 1 := by simpa only [d159948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11221 p hg
    simpa only [d159948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d159948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11223 (p : Pattern) (guard : d159949 p = 1) : d47807 p ≤ (-1 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d159948 p = 1 := by simpa only [d159949, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11222 p hg
    simpa only [d159949, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159949, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d159949, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11224 (p : Pattern) (guard : d159950 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159950, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d159950, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159949 p = 1 := by simpa only [d159950, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11223 p hg
    simpa only [d159950, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11225 (p : Pattern) (guard : d159951 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d159950 p = 1 := by simpa only [d159951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11224 p hg
    simpa only [d159951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159842 p = 1 := by simpa only [d159951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11090 p hg
    simpa only [d159951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11226 (p : Pattern) (guard : d159952 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d159951 p = 1 := by simpa only [d159952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11225 p hg
    simpa only [d159952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d159952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11227 (p : Pattern) (guard : d159953 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d159952 p = 1 := by simpa only [d159953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11226 p hg
    simpa only [d159953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d159953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11228 (p : Pattern) (guard : d159954 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d159953 p = 1 := by simpa only [d159954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11227 p hg
    simpa only [d159954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d159954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11229 (p : Pattern) (guard : d159955 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159954 p = 1 := by simpa only [d159955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11228 p hg
    simpa only [d159955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159846 p = 1 := by simpa only [d159955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11094 p hg
    simpa only [d159955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11230 (p : Pattern) (guard : d159956 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d159955 p = 1 := by simpa only [d159956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11229 p hg
    simpa only [d159956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d159956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11231 (p : Pattern) (guard : d159957 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159956 p = 1 := by simpa only [d159957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11230 p hg
    simpa only [d159957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159848 p = 1 := by simpa only [d159957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11096 p hg
    simpa only [d159957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11232 (p : Pattern) (guard : d159958 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d159958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159957 p = 1 := by simpa only [d159958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11231 p hg
    simpa only [d159958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11233 (p : Pattern) (guard : d159959 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d159959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159958 p = 1 := by simpa only [d159959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11232 p hg
    simpa only [d159959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11234 (p : Pattern) (guard : d159960 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159960, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159960, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159959 p = 1 := by simpa only [d159960, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11233 p hg
    simpa only [d159960, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11235 (p : Pattern) (guard : d159961 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d159961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159960 p = 1 := by simpa only [d159961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11234 p hg
    simpa only [d159961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11236 (p : Pattern) (guard : d159962 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 69 with
  | false =>
    have hg : d159961 p = 1 := by simpa only [d159962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11235 p hg
    simpa only [d159962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d159962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11237 (p : Pattern) (guard : d159963 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 51 with
  | false =>
    have hg : d159962 p = 1 := by simpa only [d159963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11236 p hg
    simpa only [d159963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d159963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11238 (p : Pattern) (guard : d159964 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 50 with
  | false =>
    have hg : d159963 p = 1 := by simpa only [d159964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11237 p hg
    simpa only [d159964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d159964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11239 (p : Pattern) (guard : d159965 p = 1) : d47865 p ≤ (-1 : Int) + d159794 p := by
  cases selected : p 49 with
  | false =>
    have hg : d159964 p = 1 := by simpa only [d159965, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11238 p hg
    simpa only [d159965, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159965, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11105 p hg
    simpa only [d159965, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11240 (p : Pattern) (guard : d159966 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 48 with
  | false =>
    have hg : d159940 p = 1 := by simpa only [d159966, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11210 p hg
    simpa only [d159966, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159965 p = 1 := by simpa only [d159966, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11239 p hg
    simpa only [d159966, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11241 (p : Pattern) (guard : d159967 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d159967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159966 p = 1 := by simpa only [d159967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11240 p hg
    simpa only [d159967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11242 (p : Pattern) (guard : d159968 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d159968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159967 p = 1 := by simpa only [d159968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11241 p hg
    simpa only [d159968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11243 (p : Pattern) (guard : d159969 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d159969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159968 p = 1 := by simpa only [d159969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11242 p hg
    simpa only [d159969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11244 (p : Pattern) (guard : d159970 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d159970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159969 p = 1 := by simpa only [d159970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11243 p hg
    simpa only [d159970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11245 (p : Pattern) (guard : d159971 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d159971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159970 p = 1 := by simpa only [d159971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11244 p hg
    simpa only [d159971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11246 (p : Pattern) (guard : d159972 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d159863 p = 1 := by simpa only [d159972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11112 p hg
    simpa only [d159972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159971 p = 1 := by simpa only [d159972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11245 p hg
    simpa only [d159972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11247 (p : Pattern) (guard : d159973 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159905 p = 1 := by simpa only [d159973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11156 p hg
    simpa only [d159973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11248 (p : Pattern) (guard : d159974 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159973 p = 1 := by simpa only [d159974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11247 p hg
    simpa only [d159974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11249 (p : Pattern) (guard : d159975 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159974 p = 1 := by simpa only [d159975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11248 p hg
    simpa only [d159975, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
