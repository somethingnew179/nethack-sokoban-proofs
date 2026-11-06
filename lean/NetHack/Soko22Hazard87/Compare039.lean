import NetHack.Soko22Hazard87.Compare038
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9750 (p : Pattern) (guard : d2079 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2078 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9749 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8014 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9751 (p : Pattern) (guard : d2080 p = 1) : d47735 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2079 p = 1 := by simpa only [d2080, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9750 p hg
    simpa only [d2080, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2080, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d2080, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9752 (p : Pattern) (guard : d2081 p = 1) : d47736 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2080 p = 1 := by simpa only [d2081, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9751 p hg
    simpa only [d2081, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2081, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d2081, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9753 (p : Pattern) (guard : d2082 p = 1) : d47737 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2082, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8000 p hg
    simpa only [d2082, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2081 p = 1 := by simpa only [d2082, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9752 p hg
    simpa only [d2082, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9754 (p : Pattern) (guard : d2083 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2082 p = 1 := by simpa only [d2083, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9753 p hg
    simpa only [d2083, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2083, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8021 p hg
    simpa only [d2083, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9755 (p : Pattern) (guard : d2084 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2083 p = 1 := by simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9754 p hg
    simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8023 p hg
    simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9756 (p : Pattern) (guard : d2085 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9742 p hg
    simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2084 p = 1 := by simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9755 p hg
    simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9757 (p : Pattern) (guard : d2086 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2072 p = 1 := by simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9743 p hg
    simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2085 p = 1 := by simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9756 p hg
    simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9758 (p : Pattern) (guard : d2087 p = 1) : d47756 p ≤ (-2 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2087, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7999 p hg
    simpa only [d2087, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2086 p = 1 := by simpa only [d2087, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9757 p hg
    simpa only [d2087, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9759 (p : Pattern) (guard : d2088 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2088, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7998 p hg
    simpa only [d2088, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2087 p = 1 := by simpa only [d2088, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9758 p hg
    simpa only [d2088, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9760 (p : Pattern) (guard : d2089 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2075 p = 1 := by simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9746 p hg
    simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2088 p = 1 := by simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9759 p hg
    simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9761 (p : Pattern) (guard : d2090 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2088 p = 1 := by simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9759 p hg
    simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9762 (p : Pattern) (guard : d2091 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2089 p = 1 := by simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9760 p hg
    simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2090 p = 1 := by simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9761 p hg
    simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9763 (p : Pattern) (guard : d2092 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2091 p = 1 := by simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9762 p hg
    simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9764 (p : Pattern) (guard : d2093 p = 1) : d47765 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2092 p = 1 := by simpa only [d2093, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9763 p hg
    simpa only [d2093, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2093, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8033 p hg
    simpa only [d2093, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9765 (p : Pattern) (guard : d2094 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2094, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7997 p hg
    simpa only [d2094, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2093 p = 1 := by simpa only [d2094, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9764 p hg
    simpa only [d2094, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9766 (p : Pattern) (guard : d2095 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2090 p = 1 := by simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9761 p hg
    simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9767 (p : Pattern) (guard : d2096 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2095 p = 1 := by simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9766 p hg
    simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9768 (p : Pattern) (guard : d2097 p = 1) : d47765 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2096 p = 1 := by simpa only [d2097, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9767 p hg
    simpa only [d2097, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2097, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8033 p hg
    simpa only [d2097, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9769 (p : Pattern) (guard : d2098 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2098, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7997 p hg
    simpa only [d2098, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2097 p = 1 := by simpa only [d2098, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9768 p hg
    simpa only [d2098, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9770 (p : Pattern) (guard : d2099 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2094 p = 1 := by simpa only [d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9765 p hg
    simpa only [d2099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2098 p = 1 := by simpa only [d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9769 p hg
    simpa only [d2099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9771 (p : Pattern) (guard : d2100 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d2099 p = 1 := by simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9770 p hg
    simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9772 (p : Pattern) (guard : d2101 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2100 p = 1 := by simpa only [d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9771 p hg
    simpa only [d2101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d2101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9773 (p : Pattern) (guard : d2115 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2101 p = 1 := by simpa only [d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9772 p hg
    simpa only [d2115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d2115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9774 (p : Pattern) (guard : d2103 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2098 p = 1 := by simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9769 p hg
    simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9775 (p : Pattern) (guard : d2104 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d2103 p = 1 := by simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9774 p hg
    simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9776 (p : Pattern) (guard : d2105 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2104 p = 1 := by simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9775 p hg
    simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9777 (p : Pattern) (guard : d2116 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2105 p = 1 := by simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9776 p hg
    simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9778 (p : Pattern) (guard : d2117 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2115 p = 1 := by simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9773 p hg
    simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2116 p = 1 := by simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9777 p hg
    simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9779 (p : Pattern) (guard : d2118 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d2118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2117 p = 1 := by simpa only [d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9778 p hg
    simpa only [d2118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9780 (p : Pattern) (guard : d2119 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2118 p = 1 := by simpa only [d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9779 p hg
    simpa only [d2119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d2119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9781 (p : Pattern) (guard : d2120 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d2120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2119 p = 1 := by simpa only [d2120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9780 p hg
    simpa only [d2120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9782 (p : Pattern) (guard : d2121 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d2121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2120 p = 1 := by simpa only [d2121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9781 p hg
    simpa only [d2121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9783 (p : Pattern) (guard : d53794 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53794, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53794, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2121 p = 1 := by simpa only [d53794, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9782 p hg
    simpa only [d53794, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9784 (p : Pattern) (guard : d53795 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53794 p = 1 := by simpa only [d53795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9783 p hg
    simpa only [d53795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9785 (p : Pattern) (guard : d53796 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 69 with
  | false =>
    have hg : d53795 p = 1 := by simpa only [d53796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9784 p hg
    simpa only [d53796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9786 (p : Pattern) (guard : d53797 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 51 with
  | false =>
    have hg : d53796 p = 1 := by simpa only [d53797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9785 p hg
    simpa only [d53797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9787 (p : Pattern) (guard : d53798 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 50 with
  | false =>
    have hg : d53797 p = 1 := by simpa only [d53798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9786 p hg
    simpa only [d53798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9788 (p : Pattern) (guard : d53799 p = 1) : d47768 p ≤ (-2 : Int) + d98793 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53793 p = 1 := by simpa only [d53799, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9667 p hg
    simpa only [d53799, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53798 p = 1 := by simpa only [d53799, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9787 p hg
    simpa only [d53799, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9789 (p : Pattern) (guard : d1997 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8393 p hg
    simpa only [d1997, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8057 p hg
    simpa only [d1997, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9790 (p : Pattern) (guard : d1998 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9789 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9791 (p : Pattern) (guard : d1999 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9790 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9792 (p : Pattern) (guard : d2000 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9791 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9793 (p : Pattern) (guard : d2001 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9337 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9794 (p : Pattern) (guard : d2002 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9793 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9795 (p : Pattern) (guard : d2003 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2002 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9794 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9796 (p : Pattern) (guard : d2004 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9792 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2003 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9795 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9797 (p : Pattern) (guard : d2005 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9337 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9798 (p : Pattern) (guard : d2006 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9797 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9799 (p : Pattern) (guard : d2007 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9798 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9800 (p : Pattern) (guard : d2008 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9799 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9801 (p : Pattern) (guard : d2009 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2004 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9796 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2008 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9800 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9802 (p : Pattern) (guard : d2010 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2009 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9801 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9803 (p : Pattern) (guard : d2011 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2010 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9802 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9804 (p : Pattern) (guard : d2012 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2011 p = 1 := by simpa only [d2012, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9803 p hg
    simpa only [d2012, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2012, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d2012, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9805 (p : Pattern) (guard : d2013 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9789 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9806 (p : Pattern) (guard : d2014 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9790 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9805 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9807 (p : Pattern) (guard : d2015 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1999 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9791 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9806 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9808 (p : Pattern) (guard : d2016 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d2016, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8219 p hg
    simpa only [d2016, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2016, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8057 p hg
    simpa only [d2016, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9809 (p : Pattern) (guard : d2017 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9789 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2016 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9808 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9810 (p : Pattern) (guard : d2018 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2017 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9809 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9811 (p : Pattern) (guard : d2019 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9794 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2018 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9810 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9812 (p : Pattern) (guard : d2020 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2015 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9807 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2019 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9811 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9813 (p : Pattern) (guard : d2021 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d2016 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9808 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9814 (p : Pattern) (guard : d2022 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2021 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9813 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9815 (p : Pattern) (guard : d2023 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9798 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2022 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9814 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9816 (p : Pattern) (guard : d2024 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2023 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9815 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9817 (p : Pattern) (guard : d2025 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2020 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9812 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2024 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9816 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9818 (p : Pattern) (guard : d2026 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9801 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2025 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9817 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9819 (p : Pattern) (guard : d2027 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9805 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9820 (p : Pattern) (guard : d2028 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9819 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9821 (p : Pattern) (guard : d2029 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9820 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9822 (p : Pattern) (guard : d2030 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9821 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9823 (p : Pattern) (guard : d2031 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9822 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9824 (p : Pattern) (guard : d2032 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2026 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9818 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9823 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9825 (p : Pattern) (guard : d2033 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2032 p = 1 := by simpa only [d2033, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9824 p hg
    simpa only [d2033, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2033, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d2033, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9826 (p : Pattern) (guard : d2034 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2012 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9804 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2033 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9825 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9827 (p : Pattern) (guard : d2335 p = 1) : d47652 p ≤ (-2 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2335, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d2335, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2034 p = 1 := by simpa only [d2335, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9826 p hg
    simpa only [d2335, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9828 (p : Pattern) (guard : d2035 p = 1) : d47797 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9577 p hg
    simpa only [d2035, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d2035, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9829 (p : Pattern) (guard : d2336 p = 1) : d47798 p ≤ (-2 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2335 p = 1 := by simpa only [d2336, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9827 p hg
    simpa only [d2336, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2035 p = 1 := by simpa only [d2336, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9828 p hg
    simpa only [d2336, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9830 (p : Pattern) (guard : d1997 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8409 p hg
    simpa only [d1997, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8075 p hg
    simpa only [d1997, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9831 (p : Pattern) (guard : d1998 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9830 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9832 (p : Pattern) (guard : d1999 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9831 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9833 (p : Pattern) (guard : d2000 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9832 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9834 (p : Pattern) (guard : d2001 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9383 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9835 (p : Pattern) (guard : d2002 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9834 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9836 (p : Pattern) (guard : d2003 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2002 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9835 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9837 (p : Pattern) (guard : d2004 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9833 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2003 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9838 (p : Pattern) (guard : d2005 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9383 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9839 (p : Pattern) (guard : d2006 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9838 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9840 (p : Pattern) (guard : d2007 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9839 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9841 (p : Pattern) (guard : d2008 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9840 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9842 (p : Pattern) (guard : d2009 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2004 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9837 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2008 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9841 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9843 (p : Pattern) (guard : d2010 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2009 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9842 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9844 (p : Pattern) (guard : d2011 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2010 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9843 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9845 (p : Pattern) (guard : d2012 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2011 p = 1 := by simpa only [d2012, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9844 p hg
    simpa only [d2012, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2012, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d2012, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9846 (p : Pattern) (guard : d2013 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9830 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9847 (p : Pattern) (guard : d2014 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9831 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9846 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9848 (p : Pattern) (guard : d2015 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1999 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9832 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9847 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9849 (p : Pattern) (guard : d2016 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d2016, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8235 p hg
    simpa only [d2016, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2016, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8075 p hg
    simpa only [d2016, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9850 (p : Pattern) (guard : d2017 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9830 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2016 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9849 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9851 (p : Pattern) (guard : d2018 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2017 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9850 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9852 (p : Pattern) (guard : d2019 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9835 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2018 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9851 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9853 (p : Pattern) (guard : d2020 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2015 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9848 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2019 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9852 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9854 (p : Pattern) (guard : d2021 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d2016 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9849 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9855 (p : Pattern) (guard : d2022 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2021 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9854 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9856 (p : Pattern) (guard : d2023 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9839 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2022 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9855 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9857 (p : Pattern) (guard : d2024 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2023 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9856 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9858 (p : Pattern) (guard : d2025 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2020 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9853 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2024 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9857 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9859 (p : Pattern) (guard : d2026 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9842 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2025 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9858 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9860 (p : Pattern) (guard : d2027 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9846 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9861 (p : Pattern) (guard : d2028 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9860 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9862 (p : Pattern) (guard : d2029 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9861 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9863 (p : Pattern) (guard : d2030 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9862 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9864 (p : Pattern) (guard : d2031 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9863 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9865 (p : Pattern) (guard : d2032 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2026 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9859 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9864 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9866 (p : Pattern) (guard : d2033 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2032 p = 1 := by simpa only [d2033, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9865 p hg
    simpa only [d2033, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2033, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d2033, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9867 (p : Pattern) (guard : d2034 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2012 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9845 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2033 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9866 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9868 (p : Pattern) (guard : d2035 p = 1) : d47682 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9867 p hg
    simpa only [d2035, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d2035, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9869 (p : Pattern) (guard : d2036 p = 1) : d47683 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2035 p = 1 := by simpa only [d2036, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9868 p hg
    simpa only [d2036, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2036, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d2036, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9870 (p : Pattern) (guard : d2337 p = 1) : d47799 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2336 p = 1 := by simpa only [d2337, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9829 p hg
    simpa only [d2337, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2337, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9869 p hg
    simpa only [d2337, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9871 (p : Pattern) (guard : d2338 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2337 p = 1 := by simpa only [d2338, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9870 p hg
    simpa only [d2338, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2338, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d2338, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9872 (p : Pattern) (guard : d2039 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9806 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9819 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9873 (p : Pattern) (guard : d2040 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2018 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9810 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9874 (p : Pattern) (guard : d2041 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2039 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9872 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9873 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9875 (p : Pattern) (guard : d2042 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2022 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9814 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9876 (p : Pattern) (guard : d2043 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2042 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9875 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9877 (p : Pattern) (guard : d2044 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2041 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9874 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9876 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9878 (p : Pattern) (guard : d2045 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9817 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2044 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9877 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9879 (p : Pattern) (guard : d2046 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2027 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9819 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9880 (p : Pattern) (guard : d2047 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2046 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9879 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9881 (p : Pattern) (guard : d2048 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2047 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9880 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9882 (p : Pattern) (guard : d2049 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9822 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9881 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9883 (p : Pattern) (guard : d2050 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2045 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9878 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9882 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9884 (p : Pattern) (guard : d2051 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2050 p = 1 := by simpa only [d2051, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9883 p hg
    simpa only [d2051, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2051, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d2051, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9885 (p : Pattern) (guard : d2052 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9825 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2051 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9884 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9886 (p : Pattern) (guard : d2340 p = 1) : d47652 p ≤ (-2 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2340, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d2340, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2052 p = 1 := by simpa only [d2340, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9885 p hg
    simpa only [d2340, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9887 (p : Pattern) (guard : d2053 p = 1) : d47797 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9595 p hg
    simpa only [d2053, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d2053, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9888 (p : Pattern) (guard : d2341 p = 1) : d47798 p ≤ (-2 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2340 p = 1 := by simpa only [d2341, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9886 p hg
    simpa only [d2341, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2053 p = 1 := by simpa only [d2341, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9887 p hg
    simpa only [d2341, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9889 (p : Pattern) (guard : d2039 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9847 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9860 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9890 (p : Pattern) (guard : d2040 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2018 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9851 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9891 (p : Pattern) (guard : d2041 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2039 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9889 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9890 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9892 (p : Pattern) (guard : d2042 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2022 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9855 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9893 (p : Pattern) (guard : d2043 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2042 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9892 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9894 (p : Pattern) (guard : d2044 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2041 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9891 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9893 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9895 (p : Pattern) (guard : d2045 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9858 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2044 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9894 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9896 (p : Pattern) (guard : d2046 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2027 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9860 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9897 (p : Pattern) (guard : d2047 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2046 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9896 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9898 (p : Pattern) (guard : d2048 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2047 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9897 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9899 (p : Pattern) (guard : d2049 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9863 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9898 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9900 (p : Pattern) (guard : d2050 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2045 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9895 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9899 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9901 (p : Pattern) (guard : d2051 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2050 p = 1 := by simpa only [d2051, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9900 p hg
    simpa only [d2051, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2051, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d2051, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9902 (p : Pattern) (guard : d2052 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9866 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2051 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9901 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9903 (p : Pattern) (guard : d2053 p = 1) : d47682 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9902 p hg
    simpa only [d2053, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d2053, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9904 (p : Pattern) (guard : d2054 p = 1) : d47683 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2053 p = 1 := by simpa only [d2054, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9903 p hg
    simpa only [d2054, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2054, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d2054, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9905 (p : Pattern) (guard : d2342 p = 1) : d47799 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2341 p = 1 := by simpa only [d2342, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9888 p hg
    simpa only [d2342, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2342, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9904 p hg
    simpa only [d2342, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9906 (p : Pattern) (guard : d2343 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2342 p = 1 := by simpa only [d2343, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9905 p hg
    simpa only [d2343, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2343, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d2343, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9907 (p : Pattern) (guard : d2344 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2338 p = 1 := by simpa only [d2344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9871 p hg
    simpa only [d2344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2343 p = 1 := by simpa only [d2344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9906 p hg
    simpa only [d2344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9908 (p : Pattern) (guard : d2058 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9873 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9909 (p : Pattern) (guard : d2059 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2058 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9908 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9876 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9910 (p : Pattern) (guard : d2060 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9909 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9881 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9911 (p : Pattern) (guard : d2061 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2048 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9881 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9912 (p : Pattern) (guard : d2062 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2060 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9910 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9911 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9913 (p : Pattern) (guard : d2063 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2062 p = 1 := by simpa only [d2063, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9912 p hg
    simpa only [d2063, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2063, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d2063, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9914 (p : Pattern) (guard : d2064 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9884 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2063 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9913 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9915 (p : Pattern) (guard : d2346 p = 1) : d47652 p ≤ (-2 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2346, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d2346, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2064 p = 1 := by simpa only [d2346, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9914 p hg
    simpa only [d2346, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9916 (p : Pattern) (guard : d2065 p = 1) : d47797 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9607 p hg
    simpa only [d2065, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d2065, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9917 (p : Pattern) (guard : d2347 p = 1) : d47798 p ≤ (-2 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2346 p = 1 := by simpa only [d2347, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9915 p hg
    simpa only [d2347, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2065 p = 1 := by simpa only [d2347, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9916 p hg
    simpa only [d2347, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9918 (p : Pattern) (guard : d2058 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9890 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9919 (p : Pattern) (guard : d2059 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2058 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9918 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9893 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9920 (p : Pattern) (guard : d2060 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9919 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9898 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9921 (p : Pattern) (guard : d2061 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2048 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9898 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9922 (p : Pattern) (guard : d2062 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2060 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9920 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9921 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9923 (p : Pattern) (guard : d2063 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2062 p = 1 := by simpa only [d2063, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9922 p hg
    simpa only [d2063, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2063, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d2063, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9924 (p : Pattern) (guard : d2064 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9901 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2063 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9923 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9925 (p : Pattern) (guard : d2065 p = 1) : d47682 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9924 p hg
    simpa only [d2065, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d2065, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9926 (p : Pattern) (guard : d2066 p = 1) : d47683 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2065 p = 1 := by simpa only [d2066, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9925 p hg
    simpa only [d2066, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2066, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d2066, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9927 (p : Pattern) (guard : d2348 p = 1) : d47799 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2347 p = 1 := by simpa only [d2348, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9917 p hg
    simpa only [d2348, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2348, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9926 p hg
    simpa only [d2348, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9928 (p : Pattern) (guard : d2349 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2348 p = 1 := by simpa only [d2349, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9927 p hg
    simpa only [d2349, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2349, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d2349, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9929 (p : Pattern) (guard : d2350 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2343 p = 1 := by simpa only [d2350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9906 p hg
    simpa only [d2350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2349 p = 1 := by simpa only [d2350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9928 p hg
    simpa only [d2350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9930 (p : Pattern) (guard : d2351 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2344 p = 1 := by simpa only [d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9907 p hg
    simpa only [d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2350 p = 1 := by simpa only [d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9929 p hg
    simpa only [d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9931 (p : Pattern) (guard : d2355 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2349 p = 1 := by simpa only [d2355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9928 p hg
    simpa only [d2355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8094 p hg
    simpa only [d2355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9932 (p : Pattern) (guard : d2356 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2350 p = 1 := by simpa only [d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9929 p hg
    simpa only [d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2355 p = 1 := by simpa only [d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9931 p hg
    simpa only [d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9933 (p : Pattern) (guard : d2357 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2351 p = 1 := by simpa only [d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9930 p hg
    simpa only [d2357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2356 p = 1 := by simpa only [d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9932 p hg
    simpa only [d2357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9934 (p : Pattern) (guard : d2358 p = 1) : d47804 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2358, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8054 p hg
    simpa only [d2358, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2357 p = 1 := by simpa only [d2358, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9933 p hg
    simpa only [d2358, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9935 (p : Pattern) (guard : d2359 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2359, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8053 p hg
    simpa only [d2359, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2358 p = 1 := by simpa only [d2359, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9934 p hg
    simpa only [d2359, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9936 (p : Pattern) (guard : d2076 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9909 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9937 (p : Pattern) (guard : d2077 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2076 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9936 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9938 (p : Pattern) (guard : d2078 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2077 p = 1 := by simpa only [d2078, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9937 p hg
    simpa only [d2078, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2078, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d2078, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9939 (p : Pattern) (guard : d2079 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2078 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9938 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8069 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9940 (p : Pattern) (guard : d2361 p = 1) : d47652 p ≤ (-2 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2361, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d2361, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2079 p = 1 := by simpa only [d2361, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9939 p hg
    simpa only [d2361, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9941 (p : Pattern) (guard : d2080 p = 1) : d47797 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2079 p = 1 := by simpa only [d2080, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9622 p hg
    simpa only [d2080, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2080, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d2080, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9942 (p : Pattern) (guard : d2362 p = 1) : d47798 p ≤ (-2 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2361 p = 1 := by simpa only [d2362, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9940 p hg
    simpa only [d2362, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2080 p = 1 := by simpa only [d2362, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9941 p hg
    simpa only [d2362, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9943 (p : Pattern) (guard : d2076 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9919 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9944 (p : Pattern) (guard : d2077 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2076 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9943 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9945 (p : Pattern) (guard : d2078 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2077 p = 1 := by simpa only [d2078, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9944 p hg
    simpa only [d2078, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2078, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d2078, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9946 (p : Pattern) (guard : d2079 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2078 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9945 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8087 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9947 (p : Pattern) (guard : d2080 p = 1) : d47682 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2079 p = 1 := by simpa only [d2080, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9946 p hg
    simpa only [d2080, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2080, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d2080, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9948 (p : Pattern) (guard : d2081 p = 1) : d47683 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2080 p = 1 := by simpa only [d2081, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9947 p hg
    simpa only [d2081, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2081, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d2081, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9949 (p : Pattern) (guard : d2363 p = 1) : d47799 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2362 p = 1 := by simpa only [d2363, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9942 p hg
    simpa only [d2363, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2081 p = 1 := by simpa only [d2363, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9948 p hg
    simpa only [d2363, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9950 (p : Pattern) (guard : d2364 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2363 p = 1 := by simpa only [d2364, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9949 p hg
    simpa only [d2364, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2364, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d2364, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9951 (p : Pattern) (guard : d2365 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2364 p = 1 := by simpa only [d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9950 p hg
    simpa only [d2365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8094 p hg
    simpa only [d2365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9952 (p : Pattern) (guard : d2366 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2355 p = 1 := by simpa only [d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9931 p hg
    simpa only [d2366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2365 p = 1 := by simpa only [d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9951 p hg
    simpa only [d2366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9953 (p : Pattern) (guard : d2367 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2356 p = 1 := by simpa only [d2367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9932 p hg
    simpa only [d2367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2366 p = 1 := by simpa only [d2367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9952 p hg
    simpa only [d2367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9954 (p : Pattern) (guard : d2368 p = 1) : d47804 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2368, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8054 p hg
    simpa only [d2368, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2367 p = 1 := by simpa only [d2368, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9953 p hg
    simpa only [d2368, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9955 (p : Pattern) (guard : d2369 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2369, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8053 p hg
    simpa only [d2369, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2368 p = 1 := by simpa only [d2369, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9954 p hg
    simpa only [d2369, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9956 (p : Pattern) (guard : d2370 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2359 p = 1 := by simpa only [d2370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9935 p hg
    simpa only [d2370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2369 p = 1 := by simpa only [d2370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9955 p hg
    simpa only [d2370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9957 (p : Pattern) (guard : d2375 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2369 p = 1 := by simpa only [d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9955 p hg
    simpa only [d2375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d2375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9958 (p : Pattern) (guard : d2376 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2370 p = 1 := by simpa only [d2376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9956 p hg
    simpa only [d2376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2375 p = 1 := by simpa only [d2376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9957 p hg
    simpa only [d2376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9959 (p : Pattern) (guard : d2377 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2376 p = 1 := by simpa only [d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9958 p hg
    simpa only [d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9960 (p : Pattern) (guard : d2378 p = 1) : d47807 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2377 p = 1 := by simpa only [d2378, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9959 p hg
    simpa only [d2378, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2378, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8104 p hg
    simpa only [d2378, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9961 (p : Pattern) (guard : d2379 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2379, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d2379, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2378 p = 1 := by simpa only [d2379, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9960 p hg
    simpa only [d2379, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9962 (p : Pattern) (guard : d2384 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2375 p = 1 := by simpa only [d2384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9957 p hg
    simpa only [d2384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d2384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9963 (p : Pattern) (guard : d2385 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2384 p = 1 := by simpa only [d2385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9962 p hg
    simpa only [d2385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d2385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9964 (p : Pattern) (guard : d2386 p = 1) : d47807 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2385 p = 1 := by simpa only [d2386, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9963 p hg
    simpa only [d2386, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2386, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8104 p hg
    simpa only [d2386, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9965 (p : Pattern) (guard : d2387 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2387, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d2387, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2386 p = 1 := by simpa only [d2387, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9964 p hg
    simpa only [d2387, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9966 (p : Pattern) (guard : d2388 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2379 p = 1 := by simpa only [d2388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9961 p hg
    simpa only [d2388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2387 p = 1 := by simpa only [d2388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9965 p hg
    simpa only [d2388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9967 (p : Pattern) (guard : d2389 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d2388 p = 1 := by simpa only [d2389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9966 p hg
    simpa only [d2389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d2389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9968 (p : Pattern) (guard : d2390 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2389 p = 1 := by simpa only [d2390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9967 p hg
    simpa only [d2390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d2390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9969 (p : Pattern) (guard : d2391 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2390 p = 1 := by simpa only [d2391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9968 p hg
    simpa only [d2391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d2391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9970 (p : Pattern) (guard : d2449 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2387 p = 1 := by simpa only [d2449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9965 p hg
    simpa only [d2449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d2449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9971 (p : Pattern) (guard : d2450 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d2449 p = 1 := by simpa only [d2450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9970 p hg
    simpa only [d2450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d2450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9972 (p : Pattern) (guard : d2451 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2450 p = 1 := by simpa only [d2451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9971 p hg
    simpa only [d2451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d2451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9973 (p : Pattern) (guard : d2452 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2451 p = 1 := by simpa only [d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9972 p hg
    simpa only [d2452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d2452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9974 (p : Pattern) (guard : d53800 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2391 p = 1 := by simpa only [d53800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9969 p hg
    simpa only [d53800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2452 p = 1 := by simpa only [d53800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9973 p hg
    simpa only [d53800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9975 (p : Pattern) (guard : d53801 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53800 p = 1 := by simpa only [d53801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9974 p hg
    simpa only [d53801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9976 (p : Pattern) (guard : d53802 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d53801 p = 1 := by simpa only [d53802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9975 p hg
    simpa only [d53802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9977 (p : Pattern) (guard : d53803 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53802 p = 1 := by simpa only [d53803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9976 p hg
    simpa only [d53803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9978 (p : Pattern) (guard : d53804 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53803 p = 1 := by simpa only [d53804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9977 p hg
    simpa only [d53804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9979 (p : Pattern) (guard : d53805 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53805, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53805, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53804 p = 1 := by simpa only [d53805, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9978 p hg
    simpa only [d53805, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9980 (p : Pattern) (guard : d53806 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53805 p = 1 := by simpa only [d53806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9979 p hg
    simpa only [d53806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9981 (p : Pattern) (guard : d53807 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d53806 p = 1 := by simpa only [d53807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9980 p hg
    simpa only [d53807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9982 (p : Pattern) (guard : d53808 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d53807 p = 1 := by simpa only [d53808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9981 p hg
    simpa only [d53808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9983 (p : Pattern) (guard : d53809 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d53808 p = 1 := by simpa only [d53809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9982 p hg
    simpa only [d53809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9984 (p : Pattern) (guard : d53810 p = 1) : d47865 p ≤ (-2 : Int) + d98795 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53809 p = 1 := by simpa only [d53810, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9983 p hg
    simpa only [d53810, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53810, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8121 p hg
    simpa only [d53810, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9985 (p : Pattern) (guard : d53811 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 48 with
  | false =>
    have hg : d53799 p = 1 := by simpa only [d53811, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9788 p hg
    simpa only [d53811, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53810 p = 1 := by simpa only [d53811, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9984 p hg
    simpa only [d53811, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9986 (p : Pattern) (guard : d53812 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53811 p = 1 := by simpa only [d53812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9985 p hg
    simpa only [d53812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9987 (p : Pattern) (guard : d53813 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53812 p = 1 := by simpa only [d53813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9986 p hg
    simpa only [d53813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9988 (p : Pattern) (guard : d53814 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53813 p = 1 := by simpa only [d53814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9987 p hg
    simpa only [d53814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9989 (p : Pattern) (guard : d53815 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53814 p = 1 := by simpa only [d53815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9988 p hg
    simpa only [d53815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9990 (p : Pattern) (guard : d53816 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53815 p = 1 := by simpa only [d53816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9989 p hg
    simpa only [d53816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9991 (p : Pattern) (guard : d53817 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53816 p = 1 := by simpa only [d53817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9990 p hg
    simpa only [d53817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9992 (p : Pattern) (guard : d53818 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53817 p = 1 := by simpa only [d53818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9991 p hg
    simpa only [d53818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9993 (p : Pattern) (guard : d53819 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53818 p = 1 := by simpa only [d53819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9992 p hg
    simpa only [d53819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9994 (p : Pattern) (guard : d53820 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53819 p = 1 := by simpa only [d53820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9993 p hg
    simpa only [d53820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9995 (p : Pattern) (guard : d53821 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53820 p = 1 := by simpa only [d53821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9994 p hg
    simpa only [d53821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9996 (p : Pattern) (guard : d53822 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d53791 p = 1 := by simpa only [d53822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9539 p hg
    simpa only [d53822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53821 p = 1 := by simpa only [d53822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9995 p hg
    simpa only [d53822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9997 (p : Pattern) (guard : d53823 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 260 with
  | false =>
    have hg : d53822 p = 1 := by simpa only [d53823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9996 p hg
    simpa only [d53823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9998 (p : Pattern) (guard : d53824 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 259 with
  | false =>
    have hg : d53823 p = 1 := by simpa only [d53824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9997 p hg
    simpa only [d53824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9999 (p : Pattern) (guard : d53825 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 258 with
  | false =>
    have hg : d53824 p = 1 := by simpa only [d53825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9998 p hg
    simpa only [d53825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53825, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
