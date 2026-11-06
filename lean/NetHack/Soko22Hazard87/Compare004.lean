import NetHack.Soko22Hazard87.Compare003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1000 (p : Pattern) (guard : d60857 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60854 p = 1 := by simpa only [d60857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare978 p hg
    simpa only [d60857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60856 p = 1 := by simpa only [d60857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare999 p hg
    simpa only [d60857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1001 (p : Pattern) (guard : d60858 p = 1) : d47804 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60858, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d60858, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60857 p = 1 := by simpa only [d60858, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1000 p hg
    simpa only [d60858, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1002 (p : Pattern) (guard : d60859 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60859, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d60859, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60858 p = 1 := by simpa only [d60859, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1001 p hg
    simpa only [d60859, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1003 (p : Pattern) (guard : d18371 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d18370 p = 1 := by simpa only [d18371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare997 p hg
    simpa only [d18371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d18371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1004 (p : Pattern) (guard : d60860 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60855 p = 1 := by simpa only [d60860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare998 p hg
    simpa only [d60860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18371 p = 1 := by simpa only [d60860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1003 p hg
    simpa only [d60860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1005 (p : Pattern) (guard : d60861 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60856 p = 1 := by simpa only [d60861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare999 p hg
    simpa only [d60861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60860 p = 1 := by simpa only [d60861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1004 p hg
    simpa only [d60861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1006 (p : Pattern) (guard : d60862 p = 1) : d47804 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60862, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d60862, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60861 p = 1 := by simpa only [d60862, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1005 p hg
    simpa only [d60862, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1007 (p : Pattern) (guard : d60863 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60863, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d60863, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60862 p = 1 := by simpa only [d60863, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1006 p hg
    simpa only [d60863, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1008 (p : Pattern) (guard : d60864 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60859 p = 1 := by simpa only [d60864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1002 p hg
    simpa only [d60864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60863 p = 1 := by simpa only [d60864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1007 p hg
    simpa only [d60864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1009 (p : Pattern) (guard : d2076 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare980 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1010 (p : Pattern) (guard : d2077 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2076 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1009 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1011 (p : Pattern) (guard : d2078 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2077 p = 1 := by simpa only [d2078, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1010 p hg
    simpa only [d2078, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2078, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d2078, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1012 (p : Pattern) (guard : d2079 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2078 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1011 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1013 (p : Pattern) (guard : d2361 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2361, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d2361, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2079 p = 1 := by simpa only [d2361, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1012 p hg
    simpa only [d2361, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1014 (p : Pattern) (guard : d2076 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare988 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1015 (p : Pattern) (guard : d2077 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2076 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1014 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1016 (p : Pattern) (guard : d2078 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2077 p = 1 := by simpa only [d2078, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1015 p hg
    simpa only [d2078, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2078, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d2078, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1017 (p : Pattern) (guard : d2079 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2078 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1016 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare55 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1018 (p : Pattern) (guard : d2080 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2079 p = 1 := by simpa only [d2080, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1017 p hg
    simpa only [d2080, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2080, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d2080, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1019 (p : Pattern) (guard : d2362 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2361 p = 1 := by simpa only [d2362, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1013 p hg
    simpa only [d2362, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2080 p = 1 := by simpa only [d2362, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1018 p hg
    simpa only [d2362, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1020 (p : Pattern) (guard : d60865 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2362 p = 1 := by simpa only [d60865, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1019 p hg
    simpa only [d60865, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60865, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d60865, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1021 (p : Pattern) (guard : d60866 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d60865 p = 1 := by simpa only [d60866, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1020 p hg
    simpa only [d60866, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60866, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d60866, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1022 (p : Pattern) (guard : d60867 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d60866 p = 1 := by simpa only [d60867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1021 p hg
    simpa only [d60867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d60867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1023 (p : Pattern) (guard : d60868 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d18371 p = 1 := by simpa only [d60868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1003 p hg
    simpa only [d60868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60867 p = 1 := by simpa only [d60868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1022 p hg
    simpa only [d60868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1024 (p : Pattern) (guard : d60869 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60860 p = 1 := by simpa only [d60869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1004 p hg
    simpa only [d60869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60868 p = 1 := by simpa only [d60869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1023 p hg
    simpa only [d60869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1025 (p : Pattern) (guard : d60870 p = 1) : d47804 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60870, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d60870, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60869 p = 1 := by simpa only [d60870, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1024 p hg
    simpa only [d60870, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1026 (p : Pattern) (guard : d60871 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60871, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d60871, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60870 p = 1 := by simpa only [d60871, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1025 p hg
    simpa only [d60871, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1027 (p : Pattern) (guard : d60872 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60863 p = 1 := by simpa only [d60872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1007 p hg
    simpa only [d60872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60871 p = 1 := by simpa only [d60872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1026 p hg
    simpa only [d60872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1028 (p : Pattern) (guard : d60873 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60864 p = 1 := by simpa only [d60873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1008 p hg
    simpa only [d60873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60872 p = 1 := by simpa only [d60873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1027 p hg
    simpa only [d60873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1029 (p : Pattern) (guard : d60874 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60873 p = 1 := by simpa only [d60874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1028 p hg
    simpa only [d60874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1030 (p : Pattern) (guard : d60875 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60874 p = 1 := by simpa only [d60875, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1029 p hg
    simpa only [d60875, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60875, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d60875, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1031 (p : Pattern) (guard : d60876 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60876, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d60876, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60875 p = 1 := by simpa only [d60876, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1030 p hg
    simpa only [d60876, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1032 (p : Pattern) (guard : d60877 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60871 p = 1 := by simpa only [d60877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1026 p hg
    simpa only [d60877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1033 (p : Pattern) (guard : d60878 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60872 p = 1 := by simpa only [d60878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1027 p hg
    simpa only [d60878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60877 p = 1 := by simpa only [d60878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1032 p hg
    simpa only [d60878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1034 (p : Pattern) (guard : d60879 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60878 p = 1 := by simpa only [d60879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1033 p hg
    simpa only [d60879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1035 (p : Pattern) (guard : d60880 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60879 p = 1 := by simpa only [d60880, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1034 p hg
    simpa only [d60880, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60880, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d60880, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1036 (p : Pattern) (guard : d60881 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60881, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d60881, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60880 p = 1 := by simpa only [d60881, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1035 p hg
    simpa only [d60881, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1037 (p : Pattern) (guard : d60882 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60876 p = 1 := by simpa only [d60882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1031 p hg
    simpa only [d60882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60881 p = 1 := by simpa only [d60882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1036 p hg
    simpa only [d60882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1038 (p : Pattern) (guard : d60883 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60882 p = 1 := by simpa only [d60883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1037 p hg
    simpa only [d60883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1039 (p : Pattern) (guard : d60884 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60883 p = 1 := by simpa only [d60884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1038 p hg
    simpa only [d60884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1040 (p : Pattern) (guard : d60885 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60884 p = 1 := by simpa only [d60885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1039 p hg
    simpa only [d60885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1041 (p : Pattern) (guard : d60886 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60877 p = 1 := by simpa only [d60886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1032 p hg
    simpa only [d60886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1042 (p : Pattern) (guard : d60887 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60886 p = 1 := by simpa only [d60887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1041 p hg
    simpa only [d60887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1043 (p : Pattern) (guard : d60888 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60887 p = 1 := by simpa only [d60888, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1042 p hg
    simpa only [d60888, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60888, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d60888, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1044 (p : Pattern) (guard : d60889 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60889, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d60889, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60888 p = 1 := by simpa only [d60889, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1043 p hg
    simpa only [d60889, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1045 (p : Pattern) (guard : d60890 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60881 p = 1 := by simpa only [d60890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1036 p hg
    simpa only [d60890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60889 p = 1 := by simpa only [d60890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1044 p hg
    simpa only [d60890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1046 (p : Pattern) (guard : d60891 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60890 p = 1 := by simpa only [d60891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1045 p hg
    simpa only [d60891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1047 (p : Pattern) (guard : d60892 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60891 p = 1 := by simpa only [d60892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1046 p hg
    simpa only [d60892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1048 (p : Pattern) (guard : d60893 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60892 p = 1 := by simpa only [d60893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1047 p hg
    simpa only [d60893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1049 (p : Pattern) (guard : d60894 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60885 p = 1 := by simpa only [d60894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1040 p hg
    simpa only [d60894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60893 p = 1 := by simpa only [d60894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1048 p hg
    simpa only [d60894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1050 (p : Pattern) (guard : d60895 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d60894 p = 1 := by simpa only [d60895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1049 p hg
    simpa only [d60895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1051 (p : Pattern) (guard : d60896 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60893 p = 1 := by simpa only [d60896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1048 p hg
    simpa only [d60896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1052 (p : Pattern) (guard : d60897 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d60896 p = 1 := by simpa only [d60897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1051 p hg
    simpa only [d60897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1053 (p : Pattern) (guard : d60898 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d60895 p = 1 := by simpa only [d60898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1050 p hg
    simpa only [d60898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60897 p = 1 := by simpa only [d60898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1052 p hg
    simpa only [d60898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1054 (p : Pattern) (guard : d60899 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60898 p = 1 := by simpa only [d60899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1053 p hg
    simpa only [d60899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1055 (p : Pattern) (guard : d60900 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60899 p = 1 := by simpa only [d60900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1054 p hg
    simpa only [d60900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1056 (p : Pattern) (guard : d60901 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60901, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d60901, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60900 p = 1 := by simpa only [d60901, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1055 p hg
    simpa only [d60901, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1057 (p : Pattern) (guard : d60902 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60901 p = 1 := by simpa only [d60902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1056 p hg
    simpa only [d60902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1058 (p : Pattern) (guard : d60903 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60889 p = 1 := by simpa only [d60903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1044 p hg
    simpa only [d60903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1059 (p : Pattern) (guard : d60904 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60903 p = 1 := by simpa only [d60904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1058 p hg
    simpa only [d60904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1060 (p : Pattern) (guard : d60905 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60904 p = 1 := by simpa only [d60905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1059 p hg
    simpa only [d60905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1061 (p : Pattern) (guard : d60906 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60905 p = 1 := by simpa only [d60906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1060 p hg
    simpa only [d60906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1062 (p : Pattern) (guard : d60907 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60906 p = 1 := by simpa only [d60907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1061 p hg
    simpa only [d60907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1063 (p : Pattern) (guard : d60908 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60907 p = 1 := by simpa only [d60908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1062 p hg
    simpa only [d60908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1064 (p : Pattern) (guard : d60909 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d60908 p = 1 := by simpa only [d60909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1063 p hg
    simpa only [d60909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1065 (p : Pattern) (guard : d60910 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60909 p = 1 := by simpa only [d60910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1064 p hg
    simpa only [d60910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1066 (p : Pattern) (guard : d60911 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60910 p = 1 := by simpa only [d60911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1065 p hg
    simpa only [d60911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1067 (p : Pattern) (guard : d60912 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60912, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d60912, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60911 p = 1 := by simpa only [d60912, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1066 p hg
    simpa only [d60912, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1068 (p : Pattern) (guard : d60913 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60912 p = 1 := by simpa only [d60913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1067 p hg
    simpa only [d60913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1069 (p : Pattern) (guard : d60914 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d60902 p = 1 := by simpa only [d60914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1057 p hg
    simpa only [d60914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60913 p = 1 := by simpa only [d60914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1068 p hg
    simpa only [d60914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1070 (p : Pattern) (guard : d60915 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d60914 p = 1 := by simpa only [d60915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1069 p hg
    simpa only [d60915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1071 (p : Pattern) (guard : d60916 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d60915 p = 1 := by simpa only [d60916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1070 p hg
    simpa only [d60916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1072 (p : Pattern) (guard : d60917 p = 1) : d47865 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d60916 p = 1 := by simpa only [d60917, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1071 p hg
    simpa only [d60917, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60917, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare91 p hg
    simpa only [d60917, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1073 (p : Pattern) (guard : d60918 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60918, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18 p hg
    simpa only [d60918, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60917 p = 1 := by simpa only [d60918, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1072 p hg
    simpa only [d60918, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1074 (p : Pattern) (guard : d60919 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60918 p = 1 := by simpa only [d60919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1073 p hg
    simpa only [d60919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1075 (p : Pattern) (guard : d60920 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60919 p = 1 := by simpa only [d60920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1074 p hg
    simpa only [d60920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1076 (p : Pattern) (guard : d60921 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60920 p = 1 := by simpa only [d60921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1075 p hg
    simpa only [d60921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1077 (p : Pattern) (guard : d60922 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60921 p = 1 := by simpa only [d60922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1076 p hg
    simpa only [d60922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1078 (p : Pattern) (guard : d60923 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60922 p = 1 := by simpa only [d60923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1077 p hg
    simpa only [d60923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1079 (p : Pattern) (guard : d60924 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60923 p = 1 := by simpa only [d60924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1078 p hg
    simpa only [d60924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1080 (p : Pattern) (guard : d60925 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60924 p = 1 := by simpa only [d60925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1079 p hg
    simpa only [d60925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1081 (p : Pattern) (guard : d60926 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60925 p = 1 := by simpa only [d60926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1080 p hg
    simpa only [d60926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1082 (p : Pattern) (guard : d60927 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60926 p = 1 := by simpa only [d60927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1081 p hg
    simpa only [d60927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1083 (p : Pattern) (guard : d60928 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60927 p = 1 := by simpa only [d60928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1082 p hg
    simpa only [d60928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1084 (p : Pattern) (guard : d60929 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d60851 p = 1 := by simpa only [d60929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare854 p hg
    simpa only [d60929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60928 p = 1 := by simpa only [d60929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1083 p hg
    simpa only [d60929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1085 (p : Pattern) (guard : d60930 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 260 with
  | false =>
    have hg : d60929 p = 1 := by simpa only [d60930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1084 p hg
    simpa only [d60930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1086 (p : Pattern) (guard : d60931 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 259 with
  | false =>
    have hg : d60930 p = 1 := by simpa only [d60931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1085 p hg
    simpa only [d60931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1087 (p : Pattern) (guard : d60932 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 258 with
  | false =>
    have hg : d60931 p = 1 := by simpa only [d60932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d60932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1088 (p : Pattern) (guard : d60933 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 257 with
  | false =>
    have hg : d60932 p = 1 := by simpa only [d60933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1087 p hg
    simpa only [d60933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1089 (p : Pattern) (guard : d60934 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 256 with
  | false =>
    have hg : d60933 p = 1 := by simpa only [d60934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1088 p hg
    simpa only [d60934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1090 (p : Pattern) (guard : d60935 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 255 with
  | false =>
    have hg : d60934 p = 1 := by simpa only [d60935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1089 p hg
    simpa only [d60935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1091 (p : Pattern) (guard : d60936 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 254 with
  | false =>
    have hg : d60935 p = 1 := by simpa only [d60936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1090 p hg
    simpa only [d60936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1092 (p : Pattern) (guard : d60937 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 253 with
  | false =>
    have hg : d60936 p = 1 := by simpa only [d60937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1091 p hg
    simpa only [d60937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1093 (p : Pattern) (guard : d60938 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 252 with
  | false =>
    have hg : d60937 p = 1 := by simpa only [d60938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1092 p hg
    simpa only [d60938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1094 (p : Pattern) (guard : d60939 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 251 with
  | false =>
    have hg : d60938 p = 1 := by simpa only [d60939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1093 p hg
    simpa only [d60939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1095 (p : Pattern) (guard : d60940 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 250 with
  | false =>
    have hg : d60939 p = 1 := by simpa only [d60940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1094 p hg
    simpa only [d60940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1096 (p : Pattern) (guard : d60941 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 249 with
  | false =>
    have hg : d60940 p = 1 := by simpa only [d60941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1095 p hg
    simpa only [d60941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1097 (p : Pattern) (guard : d60942 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 245 with
  | false =>
    have hg : d60941 p = 1 := by simpa only [d60942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1096 p hg
    simpa only [d60942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1098 (p : Pattern) (guard : d60943 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 200 with
  | false =>
    have hg : d60942 p = 1 := by simpa only [d60943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1097 p hg
    simpa only [d60943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1099 (p : Pattern) (guard : d60944 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 199 with
  | false =>
    have hg : d60943 p = 1 := by simpa only [d60944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1098 p hg
    simpa only [d60944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1100 (p : Pattern) (guard : d60945 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 186 with
  | false =>
    have hg : d60944 p = 1 := by simpa only [d60945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1099 p hg
    simpa only [d60945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1101 (p : Pattern) (guard : d60946 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 185 with
  | false =>
    have hg : d60945 p = 1 := by simpa only [d60946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1100 p hg
    simpa only [d60946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1102 (p : Pattern) (guard : d60947 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 184 with
  | false =>
    have hg : d60946 p = 1 := by simpa only [d60947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1101 p hg
    simpa only [d60947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1103 (p : Pattern) (guard : d60948 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 181 with
  | false =>
    have hg : d60947 p = 1 := by simpa only [d60948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1102 p hg
    simpa only [d60948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1104 (p : Pattern) (guard : d60949 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 177 with
  | false =>
    have hg : d60948 p = 1 := by simpa only [d60949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1103 p hg
    simpa only [d60949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1105 (p : Pattern) (guard : d60950 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 164 with
  | false =>
    have hg : d60949 p = 1 := by simpa only [d60950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1104 p hg
    simpa only [d60950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1106 (p : Pattern) (guard : d60951 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 156 with
  | false =>
    have hg : d60950 p = 1 := by simpa only [d60951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1105 p hg
    simpa only [d60951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1107 (p : Pattern) (guard : d60952 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 155 with
  | false =>
    have hg : d60951 p = 1 := by simpa only [d60952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1106 p hg
    simpa only [d60952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1108 (p : Pattern) (guard : d60953 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 134 with
  | false =>
    have hg : d60952 p = 1 := by simpa only [d60953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1107 p hg
    simpa only [d60953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1109 (p : Pattern) (guard : d60954 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 133 with
  | false =>
    have hg : d60953 p = 1 := by simpa only [d60954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1108 p hg
    simpa only [d60954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1110 (p : Pattern) (guard : d60955 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 120 with
  | false =>
    have hg : d60954 p = 1 := by simpa only [d60955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1109 p hg
    simpa only [d60955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1111 (p : Pattern) (guard : d60956 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 118 with
  | false =>
    have hg : d60955 p = 1 := by simpa only [d60956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1110 p hg
    simpa only [d60956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1112 (p : Pattern) (guard : d60957 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 114 with
  | false =>
    have hg : d60956 p = 1 := by simpa only [d60957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1111 p hg
    simpa only [d60957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1113 (p : Pattern) (guard : d60958 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 111 with
  | false =>
    have hg : d60957 p = 1 := by simpa only [d60958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1112 p hg
    simpa only [d60958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1114 (p : Pattern) (guard : d60959 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 98 with
  | false =>
    have hg : d60958 p = 1 := by simpa only [d60959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1113 p hg
    simpa only [d60959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1115 (p : Pattern) (guard : d60960 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 97 with
  | false =>
    have hg : d60959 p = 1 := by simpa only [d60960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1114 p hg
    simpa only [d60960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1116 (p : Pattern) (guard : d60961 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 94 with
  | false =>
    have hg : d60960 p = 1 := by simpa only [d60961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1115 p hg
    simpa only [d60961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1117 (p : Pattern) (guard : d60962 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 76 with
  | false =>
    have hg : d60961 p = 1 := by simpa only [d60962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1116 p hg
    simpa only [d60962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1118 (p : Pattern) (guard : d60963 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 67 with
  | false =>
    have hg : d60962 p = 1 := by simpa only [d60963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1117 p hg
    simpa only [d60963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1119 (p : Pattern) (guard : d60964 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 52 with
  | false =>
    have hg : d60963 p = 1 := by simpa only [d60964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1118 p hg
    simpa only [d60964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1120 (p : Pattern) (guard : d60965 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 47 with
  | false =>
    have hg : d60964 p = 1 := by simpa only [d60965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1119 p hg
    simpa only [d60965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1121 (p : Pattern) (guard : d60966 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 46 with
  | false =>
    have hg : d60965 p = 1 := by simpa only [d60966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1120 p hg
    simpa only [d60966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1122 (p : Pattern) (guard : d60967 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 45 with
  | false =>
    have hg : d60966 p = 1 := by simpa only [d60967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1121 p hg
    simpa only [d60967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1123 (p : Pattern) (guard : d60968 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 30 with
  | false =>
    have hg : d60967 p = 1 := by simpa only [d60968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1122 p hg
    simpa only [d60968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1124 (p : Pattern) (guard : d60969 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 29 with
  | false =>
    have hg : d60968 p = 1 := by simpa only [d60969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1123 p hg
    simpa only [d60969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1125 (p : Pattern) (guard : d60970 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 28 with
  | false =>
    have hg : d60969 p = 1 := by simpa only [d60970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1124 p hg
    simpa only [d60970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1126 (p : Pattern) (guard : d60971 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 27 with
  | false =>
    have hg : d60970 p = 1 := by simpa only [d60971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1125 p hg
    simpa only [d60971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1127 (p : Pattern) (guard : d60972 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 25 with
  | false =>
    have hg : d60971 p = 1 := by simpa only [d60972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1126 p hg
    simpa only [d60972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1128 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1129 (p : Pattern) (guard : d0 p = 1) : d47768 p ≤ (-1 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1130 (p : Pattern) (guard : d0 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1131 (p : Pattern) (guard : d0 p = 1) : d47700 p ≤ (-1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1132 (p : Pattern) (guard : d0 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1133 (p : Pattern) (guard : d0 p = 1) : d47697 p ≤ (-1 : Int) + d47763 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1134 (p : Pattern) (guard : d0 p = 1) : d47786 p ≤ (-1 : Int) + d47746 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1135 (p : Pattern) (guard : d0 p = 1) : d47796 p ≤ (-1 : Int) + d47751 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1136 (p : Pattern) (guard : d0 p = 1) : d47652 p ≤ (-1 : Int) + d47704 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1137 (p : Pattern) (guard : d14 p = 1) : d2 p ≤ (-1 : Int) + d3 p := by
  have ha := bounds2 p
  have hb := bounds3 p
  omega
theorem compare1138 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (-1 : Int) + d47714 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1139 (p : Pattern) (guard : d15 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1137 p hg
    simpa only [d15, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1138 p hg
    simpa only [d15, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1140 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1141 (p : Pattern) (guard : d16 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1139 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1142 (p : Pattern) (guard : d17 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1141 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1143 (p : Pattern) (guard : d18 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1142 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1144 (p : Pattern) (guard : d19 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1143 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1145 (p : Pattern) (guard : d20 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1144 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1146 (p : Pattern) (guard : d21 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d20 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1145 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1147 (p : Pattern) (guard : d22 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d21 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1146 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1148 (p : Pattern) (guard : d0 p = 1) : d47631 p ≤ (-1 : Int) + d47716 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1149 (p : Pattern) (guard : d23 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d22 p = 1 := by simpa only [d23, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1147 p hg
    simpa only [d23, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d23, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d23, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1150 (p : Pattern) (guard : d0 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1151 (p : Pattern) (guard : d24 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d23 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1149 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1150 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1152 (p : Pattern) (guard : d66 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d66, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d24 p = 1 := by simpa only [d66, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1151 p hg
    simpa only [d66, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1153 (p : Pattern) (guard : d14 p = 1) : d4 p ≤ (-1 : Int) + d5 p := by
  have ha := bounds4 p
  have hb := bounds5 p
  omega
theorem compare1154 (p : Pattern) (guard : d0 p = 1) : d47616 p ≤ (-1 : Int) + d47705 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1155 (p : Pattern) (guard : d15 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1153 p hg
    simpa only [d15, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1154 p hg
    simpa only [d15, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1156 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1157 (p : Pattern) (guard : d16 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1155 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1158 (p : Pattern) (guard : d17 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1157 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1159 (p : Pattern) (guard : d18 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1158 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1160 (p : Pattern) (guard : d19 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1159 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1161 (p : Pattern) (guard : d20 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1160 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1162 (p : Pattern) (guard : d21 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d20 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1161 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1163 (p : Pattern) (guard : d22 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d21 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1162 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1164 (p : Pattern) (guard : d0 p = 1) : d47618 p ≤ (-1 : Int) + d47707 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1165 (p : Pattern) (guard : d23 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d22 p = 1 := by simpa only [d23, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1163 p hg
    simpa only [d23, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d23, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d23, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1166 (p : Pattern) (guard : d0 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1167 (p : Pattern) (guard : d24 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d23 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1165 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1166 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1168 (p : Pattern) (guard : d0 p = 1) : d47661 p ≤ (-1 : Int) + d47659 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1169 (p : Pattern) (guard : d25 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1167 p hg
    simpa only [d25, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d25, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1170 (p : Pattern) (guard : d67 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d66 p = 1 := by simpa only [d67, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1152 p hg
    simpa only [d67, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25 p = 1 := by simpa only [d67, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1169 p hg
    simpa only [d67, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1171 (p : Pattern) (guard : d0 p = 1) : d47683 p ≤ (-1 : Int) + d47736 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1172 (p : Pattern) (guard : d17561 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d67 p = 1 := by simpa only [d17561, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1170 p hg
    simpa only [d17561, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17561, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d17561, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1173 (p : Pattern) (guard : d0 p = 1) : d47802 p ≤ (-1 : Int) + d47754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1174 (p : Pattern) (guard : d17562 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17561 p = 1 := by simpa only [d17562, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1172 p hg
    simpa only [d17562, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17562, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d17562, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1175 (p : Pattern) (guard : d0 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1176 (p : Pattern) (guard : d17563 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17562 p = 1 := by simpa only [d17563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1174 p hg
    simpa only [d17563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1175 p hg
    simpa only [d17563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1177 (p : Pattern) (guard : d17564 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17563 p = 1 := by simpa only [d17564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1176 p hg
    simpa only [d17564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1175 p hg
    simpa only [d17564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1178 (p : Pattern) (guard : d17565 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17564 p = 1 := by simpa only [d17565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1177 p hg
    simpa only [d17565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1175 p hg
    simpa only [d17565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1179 (p : Pattern) (guard : d17566 p = 1) : d47804 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17566, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1135 p hg
    simpa only [d17566, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17565 p = 1 := by simpa only [d17566, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1178 p hg
    simpa only [d17566, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1180 (p : Pattern) (guard : d17567 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17567, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1134 p hg
    simpa only [d17567, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17566 p = 1 := by simpa only [d17567, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1179 p hg
    simpa only [d17567, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1181 (p : Pattern) (guard : d0 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1182 (p : Pattern) (guard : d17568 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17567 p = 1 := by simpa only [d17568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1180 p hg
    simpa only [d17568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d17568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1183 (p : Pattern) (guard : d17569 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17568 p = 1 := by simpa only [d17569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1182 p hg
    simpa only [d17569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d17569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1184 (p : Pattern) (guard : d17570 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17569 p = 1 := by simpa only [d17570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1183 p hg
    simpa only [d17570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d17570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1185 (p : Pattern) (guard : d0 p = 1) : d47806 p ≤ (-1 : Int) + d47764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1186 (p : Pattern) (guard : d17571 p = 1) : d47807 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17570 p = 1 := by simpa only [d17571, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1184 p hg
    simpa only [d17571, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17571, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1185 p hg
    simpa only [d17571, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1187 (p : Pattern) (guard : d17572 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17572, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d17572, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17571 p = 1 := by simpa only [d17572, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1186 p hg
    simpa only [d17572, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1188 (p : Pattern) (guard : d17573 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17572 p = 1 := by simpa only [d17573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1187 p hg
    simpa only [d17573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1189 (p : Pattern) (guard : d17574 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17573 p = 1 := by simpa only [d17574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1188 p hg
    simpa only [d17574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1190 (p : Pattern) (guard : d17575 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17574 p = 1 := by simpa only [d17575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1189 p hg
    simpa only [d17575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1191 (p : Pattern) (guard : d17576 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17575 p = 1 := by simpa only [d17576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1190 p hg
    simpa only [d17576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1192 (p : Pattern) (guard : d17577 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17576 p = 1 := by simpa only [d17577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1191 p hg
    simpa only [d17577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1193 (p : Pattern) (guard : d17692 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17577 p = 1 := by simpa only [d17692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1192 p hg
    simpa only [d17692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1194 (p : Pattern) (guard : d17693 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17692 p = 1 := by simpa only [d17693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1193 p hg
    simpa only [d17693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1195 (p : Pattern) (guard : d17694 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17693 p = 1 := by simpa only [d17694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1194 p hg
    simpa only [d17694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1196 (p : Pattern) (guard : d17695 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17694 p = 1 := by simpa only [d17695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1195 p hg
    simpa only [d17695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1197 (p : Pattern) (guard : d17696 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17696, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d17696, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17695 p = 1 := by simpa only [d17696, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1196 p hg
    simpa only [d17696, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1198 (p : Pattern) (guard : d17697 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d17697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17696 p = 1 := by simpa only [d17697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1197 p hg
    simpa only [d17697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1199 (p : Pattern) (guard : d61079 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d17697 p = 1 := by simpa only [d61079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1198 p hg
    simpa only [d61079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1200 (p : Pattern) (guard : d61080 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d61079 p = 1 := by simpa only [d61080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1199 p hg
    simpa only [d61080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1201 (p : Pattern) (guard : d61081 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d61080 p = 1 := by simpa only [d61081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1200 p hg
    simpa only [d61081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1202 (p : Pattern) (guard : d0 p = 1) : d47864 p ≤ (-1 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1203 (p : Pattern) (guard : d61082 p = 1) : d47865 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d61081 p = 1 := by simpa only [d61082, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1201 p hg
    simpa only [d61082, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61082, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1202 p hg
    simpa only [d61082, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1204 (p : Pattern) (guard : d61083 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61083, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1129 p hg
    simpa only [d61083, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61082 p = 1 := by simpa only [d61083, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1203 p hg
    simpa only [d61083, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1205 (p : Pattern) (guard : d61084 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61083 p = 1 := by simpa only [d61084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1204 p hg
    simpa only [d61084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1206 (p : Pattern) (guard : d61085 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61084 p = 1 := by simpa only [d61085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1205 p hg
    simpa only [d61085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1207 (p : Pattern) (guard : d61086 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61085 p = 1 := by simpa only [d61086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1206 p hg
    simpa only [d61086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1208 (p : Pattern) (guard : d61087 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61086 p = 1 := by simpa only [d61087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d61087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1209 (p : Pattern) (guard : d61088 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61087 p = 1 := by simpa only [d61088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1208 p hg
    simpa only [d61088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1210 (p : Pattern) (guard : d128 p = 1) : d2 p ≤ (-1 : Int) + d3 p := by
  have ha := bounds2 p
  have hb := bounds3 p
  omega
theorem compare1211 (p : Pattern) (guard : d13 p = 1) : d2 p ≤ (-1 : Int) + d3 p := by
  have ha := bounds2 p
  have hb := bounds3 p
  omega
theorem compare1212 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1213 (p : Pattern) (guard : d14 p = 1) : d47629 p ≤ (-1 : Int) + d47714 p := by
  cases selected : p 247 with
  | false =>
    have hg : d13 p = 1 := by simpa only [d14, d47629, d47714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1211 p hg
    simpa only [d14, d47629, d47714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14, d47629, d47714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d14, d47629, d47714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1214 (p : Pattern) (guard : d129 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d129, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1210 p hg
    simpa only [d129, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d129, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1213 p hg
    simpa only [d129, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1215 (p : Pattern) (guard : d130 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1214 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1139 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1216 (p : Pattern) (guard : d131 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1215 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1141 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1217 (p : Pattern) (guard : d132 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1216 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1142 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1218 (p : Pattern) (guard : d133 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1217 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1219 (p : Pattern) (guard : d134 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d133 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1220 (p : Pattern) (guard : d135 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1219 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1145 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1221 (p : Pattern) (guard : d136 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d135 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1220 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1146 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1222 (p : Pattern) (guard : d137 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d136 p = 1 := by simpa only [d137, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1221 p hg
    simpa only [d137, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d137, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d137, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1223 (p : Pattern) (guard : d138 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1222 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d23 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1149 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1224 (p : Pattern) (guard : d226 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d226, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d226, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d138 p = 1 := by simpa only [d226, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1223 p hg
    simpa only [d226, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1225 (p : Pattern) (guard : d128 p = 1) : d4 p ≤ (-1 : Int) + d5 p := by
  have ha := bounds4 p
  have hb := bounds5 p
  omega
theorem compare1226 (p : Pattern) (guard : d13 p = 1) : d4 p ≤ (-1 : Int) + d5 p := by
  have ha := bounds4 p
  have hb := bounds5 p
  omega
theorem compare1227 (p : Pattern) (guard : d14 p = 1) : d47616 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 247 with
  | false =>
    have hg : d13 p = 1 := by simpa only [d14, d47616, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1226 p hg
    simpa only [d14, d47616, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14, d47616, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d14, d47616, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1228 (p : Pattern) (guard : d129 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d129, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1225 p hg
    simpa only [d129, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d129, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1227 p hg
    simpa only [d129, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1229 (p : Pattern) (guard : d130 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1228 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1155 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1230 (p : Pattern) (guard : d131 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1229 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1157 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1231 (p : Pattern) (guard : d132 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1230 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1158 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1232 (p : Pattern) (guard : d133 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1231 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1233 (p : Pattern) (guard : d134 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d133 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1232 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1234 (p : Pattern) (guard : d135 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1233 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1161 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1235 (p : Pattern) (guard : d136 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d135 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1234 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1162 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1236 (p : Pattern) (guard : d137 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d136 p = 1 := by simpa only [d137, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1235 p hg
    simpa only [d137, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d137, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d137, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1237 (p : Pattern) (guard : d138 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1236 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d23 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1165 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1238 (p : Pattern) (guard : d139 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d138 p = 1 := by simpa only [d139, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1237 p hg
    simpa only [d139, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d139, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d139, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1239 (p : Pattern) (guard : d227 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d226 p = 1 := by simpa only [d227, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1224 p hg
    simpa only [d227, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d139 p = 1 := by simpa only [d227, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1238 p hg
    simpa only [d227, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1240 (p : Pattern) (guard : d17593 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d227 p = 1 := by simpa only [d17593, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1239 p hg
    simpa only [d17593, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17593, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d17593, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1241 (p : Pattern) (guard : d17594 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17593 p = 1 := by simpa only [d17594, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1240 p hg
    simpa only [d17594, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17594, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d17594, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1242 (p : Pattern) (guard : d17595 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17594 p = 1 := by simpa only [d17595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1241 p hg
    simpa only [d17595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17562 p = 1 := by simpa only [d17595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1174 p hg
    simpa only [d17595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1243 (p : Pattern) (guard : d17596 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17595 p = 1 := by simpa only [d17596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1242 p hg
    simpa only [d17596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17563 p = 1 := by simpa only [d17596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1176 p hg
    simpa only [d17596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1244 (p : Pattern) (guard : d17597 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17596 p = 1 := by simpa only [d17597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1243 p hg
    simpa only [d17597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17564 p = 1 := by simpa only [d17597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1177 p hg
    simpa only [d17597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1245 (p : Pattern) (guard : d17598 p = 1) : d47804 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17598, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1135 p hg
    simpa only [d17598, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17597 p = 1 := by simpa only [d17598, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1244 p hg
    simpa only [d17598, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1246 (p : Pattern) (guard : d17599 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17599, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1134 p hg
    simpa only [d17599, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17598 p = 1 := by simpa only [d17599, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1245 p hg
    simpa only [d17599, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1247 (p : Pattern) (guard : d17600 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17599 p = 1 := by simpa only [d17600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d17600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17567 p = 1 := by simpa only [d17600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1180 p hg
    simpa only [d17600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1248 (p : Pattern) (guard : d17601 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17600 p = 1 := by simpa only [d17601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d17601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17568 p = 1 := by simpa only [d17601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1182 p hg
    simpa only [d17601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1249 (p : Pattern) (guard : d17602 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17601 p = 1 := by simpa only [d17602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1248 p hg
    simpa only [d17602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d17602, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
