/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons162
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare22820 (p : Pattern) (guard : d5537 p = 1) : d2793 p ≤ (0 : Int) + d2020 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2793, d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22643 p hg
    simpa only [d2793, d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2793, d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22819 p hg
    simpa only [d2793, d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22821 (p : Pattern) (guard : d5537 p = 1) : d2794 p ≤ (0 : Int) + d2021 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2794, d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22598 p hg
    simpa only [d2794, d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2794, d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22582 p hg
    simpa only [d2794, d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22822 (p : Pattern) (guard : d5537 p = 1) : d2795 p ≤ (0 : Int) + d2022 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2795, d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22645 p hg
    simpa only [d2795, d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2795, d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2795, d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22823 (p : Pattern) (guard : d5537 p = 1) : d2796 p ≤ (0 : Int) + d2023 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2796, d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22821 p hg
    simpa only [d2796, d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2796, d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22822 p hg
    simpa only [d2796, d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22824 (p : Pattern) (guard : d5537 p = 1) : d2797 p ≤ (0 : Int) + d2024 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2797, d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22820 p hg
    simpa only [d2797, d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2797, d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22823 p hg
    simpa only [d2797, d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22825 (p : Pattern) (guard : d5537 p = 1) : d2798 p ≤ (0 : Int) + d2025 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2798, d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22615 p hg
    simpa only [d2798, d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2798, d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22822 p hg
    simpa only [d2798, d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22826 (p : Pattern) (guard : d5537 p = 1) : d2799 p ≤ (0 : Int) + d2026 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2799, d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22825 p hg
    simpa only [d2799, d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2799, d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22622 p hg
    simpa only [d2799, d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22827 (p : Pattern) (guard : d5537 p = 1) : d2800 p ≤ (0 : Int) + d2027 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2800, d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22824 p hg
    simpa only [d2800, d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2800, d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22826 p hg
    simpa only [d2800, d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22828 (p : Pattern) (guard : d5537 p = 1) : d2801 p ≤ (0 : Int) + d2028 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2801, d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22818 p hg
    simpa only [d2801, d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2801, d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22827 p hg
    simpa only [d2801, d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22829 (p : Pattern) (guard : d5537 p = 1) : d2543 p ≤ (0 : Int) + d2031 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2543, d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21180 p hg
    simpa only [d5537, d2543, d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2543, d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2543, d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22830 (p : Pattern) (guard : d5537 p = 1) : d2611 p ≤ (0 : Int) + d2032 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2611, d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22598 p hg
    simpa only [d2611, d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2611, d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22829 p hg
    simpa only [d2611, d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22831 (p : Pattern) (guard : d5537 p = 1) : d2618 p ≤ (0 : Int) + d2033 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2618, d2033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22628 p hg
    simpa only [d2618, d2033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2618, d2033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22830 p hg
    simpa only [d2618, d2033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22832 (p : Pattern) (guard : d5537 p = 1) : d2619 p ≤ (0 : Int) + d2034 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2619, d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22814 p hg
    simpa only [d2619, d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2619, d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22639 p hg
    simpa only [d2619, d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22833 (p : Pattern) (guard : d5537 p = 1) : d2620 p ≤ (0 : Int) + d2035 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2620, d2035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22831 p hg
    simpa only [d2620, d2035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2620, d2035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22832 p hg
    simpa only [d2620, d2035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22834 (p : Pattern) (guard : d5537 p = 1) : d2621 p ≤ (0 : Int) + d2036 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2621, d2036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22814 p hg
    simpa only [d2621, d2036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2621, d2036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22607 p hg
    simpa only [d2621, d2036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22835 (p : Pattern) (guard : d5537 p = 1) : d2622 p ≤ (0 : Int) + d2037 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2622, d2037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22834 p hg
    simpa only [d2622, d2037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2622, d2037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22612 p hg
    simpa only [d2622, d2037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22836 (p : Pattern) (guard : d5537 p = 1) : d2623 p ≤ (0 : Int) + d2038 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2623, d2038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22833 p hg
    simpa only [d2623, d2038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2623, d2038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22835 p hg
    simpa only [d2623, d2038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22837 (p : Pattern) (guard : d5537 p = 1) : d2802 p ≤ (0 : Int) + d2039 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2802, d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22819 p hg
    simpa only [d2802, d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2802, d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22584 p hg
    simpa only [d2802, d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22838 (p : Pattern) (guard : d5537 p = 1) : d2803 p ≤ (0 : Int) + d2040 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2803, d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22822 p hg
    simpa only [d2803, d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2803, d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22621 p hg
    simpa only [d2803, d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22839 (p : Pattern) (guard : d5537 p = 1) : d2804 p ≤ (0 : Int) + d2041 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2804, d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22837 p hg
    simpa only [d2804, d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2804, d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22838 p hg
    simpa only [d2804, d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22840 (p : Pattern) (guard : d5537 p = 1) : d2805 p ≤ (0 : Int) + d2042 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2805, d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22822 p hg
    simpa only [d2805, d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2805, d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2805, d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22841 (p : Pattern) (guard : d5537 p = 1) : d2806 p ≤ (0 : Int) + d2043 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2806, d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22840 p hg
    simpa only [d2806, d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2806, d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2806, d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22842 (p : Pattern) (guard : d5537 p = 1) : d2807 p ≤ (0 : Int) + d2044 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2807, d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22839 p hg
    simpa only [d2807, d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2807, d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22841 p hg
    simpa only [d2807, d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22843 (p : Pattern) (guard : d5537 p = 1) : d2808 p ≤ (0 : Int) + d2045 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2808, d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22836 p hg
    simpa only [d2808, d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2808, d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22842 p hg
    simpa only [d2808, d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22844 (p : Pattern) (guard : d5537 p = 1) : d2809 p ≤ (0 : Int) + d2046 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2809, d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22828 p hg
    simpa only [d2809, d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2809, d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22843 p hg
    simpa only [d2809, d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22845 (p : Pattern) (guard : d5537 p = 1) : d2600 p ≤ (0 : Int) + d2049 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2600, d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21218 p hg
    simpa only [d5537, d2600, d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2600, d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2600, d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22846 (p : Pattern) (guard : d5537 p = 1) : d2601 p ≤ (0 : Int) + d2050 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2601, d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22562 p hg
    simpa only [d2601, d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2601, d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22845 p hg
    simpa only [d2601, d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22847 (p : Pattern) (guard : d5537 p = 1) : d2600 p ≤ (0 : Int) + d2055 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2600, d2055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21224 p hg
    simpa only [d5537, d2600, d2055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2600, d2055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2600, d2055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22848 (p : Pattern) (guard : d5537 p = 1) : d2601 p ≤ (0 : Int) + d2056 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2601, d2056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22562 p hg
    simpa only [d2601, d2056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2601, d2056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22847 p hg
    simpa only [d2601, d2056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22849 (p : Pattern) (guard : d5537 p = 1) : d2601 p ≤ (0 : Int) + d2057 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22846 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22848 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22850 (p : Pattern) (guard : d5537 p = 1) : d2810 p ≤ (0 : Int) + d2058 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2810, d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22849 p hg
    simpa only [d2810, d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2810, d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22647 p hg
    simpa only [d2810, d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22851 (p : Pattern) (guard : d5537 p = 1) : d2811 p ≤ (0 : Int) + d2059 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2811, d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22850 p hg
    simpa only [d2811, d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2811, d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22648 p hg
    simpa only [d2811, d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22852 (p : Pattern) (guard : d0 p = 1) : d2813 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22853 (p : Pattern) (guard : d5537 p = 1) : d2814 p ≤ (0 : Int) + d192 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2814, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21511 p hg
    simpa only [d5537, d2814, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2814, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22852 p hg
    simpa only [d5537, d2814, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22854 (p : Pattern) (guard : d5537 p = 1) : d2815 p ≤ (0 : Int) + d2062 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2815, d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21514 p hg
    simpa only [d5537, d2815, d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2815, d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2815, d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22855 (p : Pattern) (guard : d5537 p = 1) : d2816 p ≤ (0 : Int) + d2063 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2816, d2063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22853 p hg
    simpa only [d2816, d2063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2816, d2063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22854 p hg
    simpa only [d2816, d2063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22856 (p : Pattern) (guard : d5537 p = 1) : d2817 p ≤ (0 : Int) + d2064 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2817, d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22635 p hg
    simpa only [d2817, d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2817, d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22855 p hg
    simpa only [d2817, d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22857 (p : Pattern) (guard : d5537 p = 1) : d2818 p ≤ (0 : Int) + d2065 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2818, d2065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22856 p hg
    simpa only [d2818, d2065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2818, d2065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2818, d2065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22858 (p : Pattern) (guard : d5537 p = 1) : d2819 p ≤ (0 : Int) + d2066 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2819, d2066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22857 p hg
    simpa only [d2819, d2066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2819, d2066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2819, d2066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22859 (p : Pattern) (guard : d5537 p = 1) : d2820 p ≤ (0 : Int) + d2067 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2820, d2067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22851 p hg
    simpa only [d2820, d2067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2820, d2067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22858 p hg
    simpa only [d2820, d2067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22860 (p : Pattern) (guard : d5537 p = 1) : d2543 p ≤ (0 : Int) + d2072 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2543, d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21524 p hg
    simpa only [d5537, d2543, d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2543, d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2543, d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22861 (p : Pattern) (guard : d5537 p = 1) : d2611 p ≤ (0 : Int) + d2073 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2611, d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22598 p hg
    simpa only [d2611, d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2611, d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22860 p hg
    simpa only [d2611, d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22862 (p : Pattern) (guard : d5537 p = 1) : d2611 p ≤ (0 : Int) + d2074 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22861 p hg
    simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22643 p hg
    simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22863 (p : Pattern) (guard : d5537 p = 1) : d2821 p ≤ (0 : Int) + d2075 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2821, d2075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22635 p hg
    simpa only [d2821, d2075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2821, d2075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22611 p hg
    simpa only [d2821, d2075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22864 (p : Pattern) (guard : d5537 p = 1) : d2822 p ≤ (0 : Int) + d2076 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2822, d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22862 p hg
    simpa only [d2822, d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2822, d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22863 p hg
    simpa only [d2822, d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22865 (p : Pattern) (guard : d5537 p = 1) : d2823 p ≤ (0 : Int) + d2077 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2823, d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22864 p hg
    simpa only [d2823, d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2823, d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22658 p hg
    simpa only [d2823, d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22866 (p : Pattern) (guard : d5537 p = 1) : d2824 p ≤ (0 : Int) + d2078 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2824, d2078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22855 p hg
    simpa only [d2824, d2078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2824, d2078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2824, d2078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22867 (p : Pattern) (guard : d5537 p = 1) : d2825 p ≤ (0 : Int) + d2079 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2825, d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22866 p hg
    simpa only [d2825, d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2825, d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2825, d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22868 (p : Pattern) (guard : d5537 p = 1) : d2826 p ≤ (0 : Int) + d2080 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2826, d2080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22867 p hg
    simpa only [d2826, d2080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2826, d2080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2826, d2080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22869 (p : Pattern) (guard : d5537 p = 1) : d2827 p ≤ (0 : Int) + d2081 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2827, d2081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22865 p hg
    simpa only [d2827, d2081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2827, d2081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22868 p hg
    simpa only [d2827, d2081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22870 (p : Pattern) (guard : d5537 p = 1) : d2828 p ≤ (0 : Int) + d2082 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2828, d2082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22859 p hg
    simpa only [d2828, d2082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2828, d2082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22869 p hg
    simpa only [d2828, d2082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22871 (p : Pattern) (guard : d5537 p = 1) : d2829 p ≤ (0 : Int) + d2083 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2829, d2083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22844 p hg
    simpa only [d2829, d2083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2829, d2083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22870 p hg
    simpa only [d2829, d2083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22872 (p : Pattern) (guard : d5537 p = 1) : d2830 p ≤ (0 : Int) + d2084 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2830, d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22870 p hg
    simpa only [d2830, d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2830, d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2830, d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22873 (p : Pattern) (guard : d5537 p = 1) : d2831 p ≤ (0 : Int) + d2085 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2831, d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22871 p hg
    simpa only [d2831, d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2831, d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22872 p hg
    simpa only [d2831, d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22874 (p : Pattern) (guard : d5537 p = 1) : d2832 p ≤ (0 : Int) + d2086 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2832, d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22699 p hg
    simpa only [d2832, d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2832, d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22873 p hg
    simpa only [d2832, d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22875 (p : Pattern) (guard : d5537 p = 1) : d2833 p ≤ (0 : Int) + d2087 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2833, d2087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22685 p hg
    simpa only [d2833, d2087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2833, d2087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22874 p hg
    simpa only [d2833, d2087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22876 (p : Pattern) (guard : d5537 p = 1) : d2834 p ≤ (0 : Int) + d2088 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2834, d2088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22719 p hg
    simpa only [d2834, d2088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2834, d2088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2834, d2088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22877 (p : Pattern) (guard : d5537 p = 1) : d2835 p ≤ (0 : Int) + d2089 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2835, d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22745 p hg
    simpa only [d2835, d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2835, d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22876 p hg
    simpa only [d2835, d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22878 (p : Pattern) (guard : d5537 p = 1) : d2836 p ≤ (0 : Int) + d2090 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2836, d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22876 p hg
    simpa only [d2836, d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2836, d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2836, d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22879 (p : Pattern) (guard : d5537 p = 1) : d2837 p ≤ (0 : Int) + d2091 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2837, d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22877 p hg
    simpa only [d2837, d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2837, d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22878 p hg
    simpa only [d2837, d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22880 (p : Pattern) (guard : d5537 p = 1) : d2838 p ≤ (0 : Int) + d2092 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2838, d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22731 p hg
    simpa only [d2838, d2092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2838, d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2838, d2092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22881 (p : Pattern) (guard : d5537 p = 1) : d2839 p ≤ (0 : Int) + d2093 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2839, d2093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22752 p hg
    simpa only [d2839, d2093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2839, d2093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22880 p hg
    simpa only [d2839, d2093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22882 (p : Pattern) (guard : d5537 p = 1) : d2840 p ≤ (0 : Int) + d2094 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2840, d2094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22880 p hg
    simpa only [d2840, d2094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2840, d2094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2840, d2094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22883 (p : Pattern) (guard : d5537 p = 1) : d2841 p ≤ (0 : Int) + d2095 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2841, d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22881 p hg
    simpa only [d2841, d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2841, d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22882 p hg
    simpa only [d2841, d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22884 (p : Pattern) (guard : d5537 p = 1) : d2842 p ≤ (0 : Int) + d2096 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2842, d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22879 p hg
    simpa only [d2842, d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2842, d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22883 p hg
    simpa only [d2842, d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22885 (p : Pattern) (guard : d5537 p = 1) : d2843 p ≤ (0 : Int) + d2097 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2843, d2097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22737 p hg
    simpa only [d2843, d2097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2843, d2097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22884 p hg
    simpa only [d2843, d2097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22886 (p : Pattern) (guard : d5537 p = 1) : d2844 p ≤ (0 : Int) + d2098 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2844, d2098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22768 p hg
    simpa only [d2844, d2098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2844, d2098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2844, d2098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22887 (p : Pattern) (guard : d5537 p = 1) : d2845 p ≤ (0 : Int) + d2099 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2845, d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22781 p hg
    simpa only [d2845, d2099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2845, d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22886 p hg
    simpa only [d2845, d2099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22888 (p : Pattern) (guard : d5537 p = 1) : d2846 p ≤ (0 : Int) + d2100 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2846, d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22886 p hg
    simpa only [d2846, d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2846, d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2846, d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22889 (p : Pattern) (guard : d5537 p = 1) : d2847 p ≤ (0 : Int) + d2101 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2847, d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22887 p hg
    simpa only [d2847, d2101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2847, d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22888 p hg
    simpa only [d2847, d2101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22890 (p : Pattern) (guard : d5537 p = 1) : d2848 p ≤ (0 : Int) + d2102 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2848, d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22889 p hg
    simpa only [d2848, d2102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2848, d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22789 p hg
    simpa only [d2848, d2102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22891 (p : Pattern) (guard : d5537 p = 1) : d2849 p ≤ (0 : Int) + d2103 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2849, d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22780 p hg
    simpa only [d2849, d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2849, d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22890 p hg
    simpa only [d2849, d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22892 (p : Pattern) (guard : d5537 p = 1) : d2850 p ≤ (0 : Int) + d2104 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2850, d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22885 p hg
    simpa only [d2850, d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2850, d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22891 p hg
    simpa only [d2850, d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22893 (p : Pattern) (guard : d5537 p = 1) : d2851 p ≤ (0 : Int) + d2105 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2851, d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22891 p hg
    simpa only [d2851, d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2851, d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22796 p hg
    simpa only [d2851, d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22894 (p : Pattern) (guard : d5537 p = 1) : d2852 p ≤ (0 : Int) + d2106 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2852, d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22892 p hg
    simpa only [d2852, d2106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2852, d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22893 p hg
    simpa only [d2852, d2106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22895 (p : Pattern) (guard : d5537 p = 1) : d2745 p ≤ (0 : Int) + d2109 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2745, d2109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21403 p hg
    simpa only [d5537, d2745, d2109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2745, d2109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2745, d2109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22896 (p : Pattern) (guard : d5537 p = 1) : d2746 p ≤ (0 : Int) + d2110 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2746, d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22713 p hg
    simpa only [d2746, d2110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2746, d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22895 p hg
    simpa only [d2746, d2110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22897 (p : Pattern) (guard : d5537 p = 1) : d2749 p ≤ (0 : Int) + d2111 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2749, d2111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22896 p hg
    simpa only [d2749, d2111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2749, d2111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22768 p hg
    simpa only [d2749, d2111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22898 (p : Pattern) (guard : d5537 p = 1) : d2750 p ≤ (0 : Int) + d2112 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2750, d2112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22761 p hg
    simpa only [d2750, d2112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2750, d2112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22897 p hg
    simpa only [d2750, d2112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22899 (p : Pattern) (guard : d5537 p = 1) : d2749 p ≤ (0 : Int) + d2113 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2749, d2113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22763 p hg
    simpa only [d2749, d2113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2749, d2113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22768 p hg
    simpa only [d2749, d2113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22900 (p : Pattern) (guard : d5537 p = 1) : d2751 p ≤ (0 : Int) + d2114 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2751, d2114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22899 p hg
    simpa only [d2751, d2114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2751, d2114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22722 p hg
    simpa only [d2751, d2114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22901 (p : Pattern) (guard : d5537 p = 1) : d2752 p ≤ (0 : Int) + d2115 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2752, d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22898 p hg
    simpa only [d2752, d2115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2752, d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22900 p hg
    simpa only [d2752, d2115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22902 (p : Pattern) (guard : d5537 p = 1) : d2853 p ≤ (0 : Int) + d2116 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2853, d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22742 p hg
    simpa only [d2853, d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2853, d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22727 p hg
    simpa only [d2853, d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22903 (p : Pattern) (guard : d5537 p = 1) : d2854 p ≤ (0 : Int) + d2117 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2854, d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22773 p hg
    simpa only [d2854, d2117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2854, d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22902 p hg
    simpa only [d2854, d2117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22904 (p : Pattern) (guard : d5537 p = 1) : d2855 p ≤ (0 : Int) + d2118 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2855, d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22903 p hg
    simpa only [d2855, d2118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2855, d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22880 p hg
    simpa only [d2855, d2118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22905 (p : Pattern) (guard : d5537 p = 1) : d2856 p ≤ (0 : Int) + d2119 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2856, d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22775 p hg
    simpa only [d2856, d2119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2856, d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2856, d2119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22906 (p : Pattern) (guard : d5537 p = 1) : d2857 p ≤ (0 : Int) + d2120 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2857, d2120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22905 p hg
    simpa only [d2857, d2120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2857, d2120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2857, d2120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22907 (p : Pattern) (guard : d5537 p = 1) : d2858 p ≤ (0 : Int) + d2121 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2858, d2121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22906 p hg
    simpa only [d2858, d2121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2858, d2121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2858, d2121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22908 (p : Pattern) (guard : d5537 p = 1) : d2859 p ≤ (0 : Int) + d2122 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2859, d2122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22904 p hg
    simpa only [d2859, d2122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2859, d2122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22907 p hg
    simpa only [d2859, d2122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22909 (p : Pattern) (guard : d5537 p = 1) : d2860 p ≤ (0 : Int) + d2123 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2860, d2123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22901 p hg
    simpa only [d2860, d2123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2860, d2123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22908 p hg
    simpa only [d2860, d2123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22910 (p : Pattern) (guard : d5537 p = 1) : d2705 p ≤ (0 : Int) + d2126 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2705, d2126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21379 p hg
    simpa only [d5537, d2705, d2126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2705, d2126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2705, d2126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22911 (p : Pattern) (guard : d5537 p = 1) : d2753 p ≤ (0 : Int) + d2127 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2753, d2127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22742 p hg
    simpa only [d2753, d2127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2753, d2127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22910 p hg
    simpa only [d2753, d2127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22912 (p : Pattern) (guard : d5537 p = 1) : d2760 p ≤ (0 : Int) + d2128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2760, d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22896 p hg
    simpa only [d2760, d2128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2760, d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22911 p hg
    simpa only [d2760, d2128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22913 (p : Pattern) (guard : d5537 p = 1) : d2747 p ≤ (0 : Int) + d2131 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2747, d2131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21329 p hg
    simpa only [d5537, d2747, d2131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2747, d2131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2747, d2131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22914 (p : Pattern) (guard : d5537 p = 1) : d2748 p ≤ (0 : Int) + d2132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2748, d2132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22717 p hg
    simpa only [d2748, d2132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2748, d2132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22913 p hg
    simpa only [d2748, d2132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22915 (p : Pattern) (guard : d5537 p = 1) : d2844 p ≤ (0 : Int) + d2133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2844, d2133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22914 p hg
    simpa only [d2844, d2133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2844, d2133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2844, d2133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22916 (p : Pattern) (guard : d5537 p = 1) : d2845 p ≤ (0 : Int) + d2134 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2845, d2134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22912 p hg
    simpa only [d2845, d2134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2845, d2134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22915 p hg
    simpa only [d2845, d2134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22917 (p : Pattern) (guard : d5537 p = 1) : d2747 p ≤ (0 : Int) + d2137 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2747, d2137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21583 p hg
    simpa only [d5537, d2747, d2137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2747, d2137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2747, d2137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22918 (p : Pattern) (guard : d5537 p = 1) : d2748 p ≤ (0 : Int) + d2138 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2748, d2138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22717 p hg
    simpa only [d2748, d2138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2748, d2138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22917 p hg
    simpa only [d2748, d2138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22919 (p : Pattern) (guard : d5537 p = 1) : d2844 p ≤ (0 : Int) + d2139 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2844, d2139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22918 p hg
    simpa only [d2844, d2139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2844, d2139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2844, d2139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22920 (p : Pattern) (guard : d5537 p = 1) : d2846 p ≤ (0 : Int) + d2140 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2846, d2140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22919 p hg
    simpa only [d2846, d2140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2846, d2140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2846, d2140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22921 (p : Pattern) (guard : d5537 p = 1) : d2847 p ≤ (0 : Int) + d2141 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2847, d2141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22916 p hg
    simpa only [d2847, d2141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2847, d2141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22920 p hg
    simpa only [d2847, d2141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22922 (p : Pattern) (guard : d5537 p = 1) : d2861 p ≤ (0 : Int) + d2142 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2861, d2142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22717 p hg
    simpa only [d2861, d2142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2861, d2142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22727 p hg
    simpa only [d2861, d2142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22923 (p : Pattern) (guard : d5537 p = 1) : d2862 p ≤ (0 : Int) + d2143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2862, d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22922 p hg
    simpa only [d2862, d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2862, d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22731 p hg
    simpa only [d2862, d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22924 (p : Pattern) (guard : d5537 p = 1) : d2863 p ≤ (0 : Int) + d2144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2863, d2144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22923 p hg
    simpa only [d2863, d2144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2863, d2144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22906 p hg
    simpa only [d2863, d2144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22925 (p : Pattern) (guard : d5537 p = 1) : d2864 p ≤ (0 : Int) + d2145 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2864, d2145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22590 p hg
    simpa only [d2864, d2145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2864, d2145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2864, d2145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22926 (p : Pattern) (guard : d5537 p = 1) : d2865 p ≤ (0 : Int) + d2146 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2865, d2146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22924 p hg
    simpa only [d2865, d2146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2865, d2146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22925 p hg
    simpa only [d2865, d2146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22927 (p : Pattern) (guard : d5537 p = 1) : d2866 p ≤ (0 : Int) + d2147 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2866, d2147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22921 p hg
    simpa only [d2866, d2147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2866, d2147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22926 p hg
    simpa only [d2866, d2147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22928 (p : Pattern) (guard : d5537 p = 1) : d2867 p ≤ (0 : Int) + d2148 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2867, d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22909 p hg
    simpa only [d2867, d2148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2867, d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22927 p hg
    simpa only [d2867, d2148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22929 (p : Pattern) (guard : d5537 p = 1) : d2746 p ≤ (0 : Int) + d2149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22763 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22766 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22930 (p : Pattern) (guard : d5537 p = 1) : d2868 p ≤ (0 : Int) + d2150 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2868, d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22773 p hg
    simpa only [d2868, d2150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2868, d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22611 p hg
    simpa only [d2868, d2150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22931 (p : Pattern) (guard : d5537 p = 1) : d2869 p ≤ (0 : Int) + d2151 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2869, d2151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22929 p hg
    simpa only [d2869, d2151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2869, d2151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22930 p hg
    simpa only [d2869, d2151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22932 (p : Pattern) (guard : d5537 p = 1) : d2870 p ≤ (0 : Int) + d2152 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2870, d2152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22931 p hg
    simpa only [d2870, d2152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2870, d2152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22785 p hg
    simpa only [d2870, d2152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22933 (p : Pattern) (guard : d5537 p = 1) : d2871 p ≤ (0 : Int) + d2153 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2871, d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22932 p hg
    simpa only [d2871, d2153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2871, d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22789 p hg
    simpa only [d2871, d2153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22934 (p : Pattern) (guard : d5537 p = 1) : d2705 p ≤ (0 : Int) + d2158 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2705, d2158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21608 p hg
    simpa only [d5537, d2705, d2158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2705, d2158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2705, d2158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22935 (p : Pattern) (guard : d5537 p = 1) : d2753 p ≤ (0 : Int) + d2159 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2753, d2159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22742 p hg
    simpa only [d2753, d2159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2753, d2159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22934 p hg
    simpa only [d2753, d2159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22936 (p : Pattern) (guard : d5537 p = 1) : d2753 p ≤ (0 : Int) + d2160 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22935 p hg
    simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22773 p hg
    simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22937 (p : Pattern) (guard : d5537 p = 1) : d2872 p ≤ (0 : Int) + d2161 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2872, d2161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22936 p hg
    simpa only [d2872, d2161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2872, d2161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22886 p hg
    simpa only [d2872, d2161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22938 (p : Pattern) (guard : d5537 p = 1) : d2873 p ≤ (0 : Int) + d2162 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2873, d2162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22937 p hg
    simpa only [d2873, d2162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2873, d2162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22788 p hg
    simpa only [d2873, d2162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22939 (p : Pattern) (guard : d5537 p = 1) : d2874 p ≤ (0 : Int) + d2163 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2874, d2163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22640 p hg
    simpa only [d2874, d2163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2874, d2163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2874, d2163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22940 (p : Pattern) (guard : d5537 p = 1) : d2875 p ≤ (0 : Int) + d2164 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2875, d2164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22939 p hg
    simpa only [d2875, d2164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2875, d2164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2875, d2164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22941 (p : Pattern) (guard : d5537 p = 1) : d2876 p ≤ (0 : Int) + d2165 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2876, d2165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22938 p hg
    simpa only [d2876, d2165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2876, d2165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22940 p hg
    simpa only [d2876, d2165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22942 (p : Pattern) (guard : d5537 p = 1) : d2877 p ≤ (0 : Int) + d2166 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2877, d2166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22933 p hg
    simpa only [d2877, d2166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2877, d2166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22941 p hg
    simpa only [d2877, d2166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22943 (p : Pattern) (guard : d5537 p = 1) : d2878 p ≤ (0 : Int) + d2167 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2878, d2167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22928 p hg
    simpa only [d2878, d2167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2878, d2167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22942 p hg
    simpa only [d2878, d2167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22944 (p : Pattern) (guard : d5537 p = 1) : d2879 p ≤ (0 : Int) + d2168 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2879, d2168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22773 p hg
    simpa only [d2879, d2168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2879, d2168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22639 p hg
    simpa only [d2879, d2168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22945 (p : Pattern) (guard : d5537 p = 1) : d2880 p ≤ (0 : Int) + d2169 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2880, d2169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22929 p hg
    simpa only [d2880, d2169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2880, d2169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22944 p hg
    simpa only [d2880, d2169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22946 (p : Pattern) (guard : d5537 p = 1) : d2881 p ≤ (0 : Int) + d2170 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2881, d2170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22768 p hg
    simpa only [d2881, d2170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2881, d2170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22639 p hg
    simpa only [d2881, d2170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22947 (p : Pattern) (guard : d5537 p = 1) : d2882 p ≤ (0 : Int) + d2171 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2882, d2171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22946 p hg
    simpa only [d2882, d2171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2882, d2171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2882, d2171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22948 (p : Pattern) (guard : d5537 p = 1) : d2883 p ≤ (0 : Int) + d2172 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2883, d2172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22945 p hg
    simpa only [d2883, d2172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2883, d2172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22947 p hg
    simpa only [d2883, d2172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22949 (p : Pattern) (guard : d5537 p = 1) : d2884 p ≤ (0 : Int) + d2173 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2884, d2173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22776 p hg
    simpa only [d2884, d2173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2884, d2173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22611 p hg
    simpa only [d2884, d2173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22950 (p : Pattern) (guard : d5537 p = 1) : d2885 p ≤ (0 : Int) + d2174 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2885, d2174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22949 p hg
    simpa only [d2885, d2174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2885, d2174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2885, d2174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22951 (p : Pattern) (guard : d5537 p = 1) : d2886 p ≤ (0 : Int) + d2175 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2886, d2175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22950 p hg
    simpa only [d2886, d2175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2886, d2175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2886, d2175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22952 (p : Pattern) (guard : d5537 p = 1) : d2887 p ≤ (0 : Int) + d2176 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2887, d2176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22948 p hg
    simpa only [d2887, d2176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2887, d2176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22951 p hg
    simpa only [d2887, d2176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22953 (p : Pattern) (guard : d5537 p = 1) : d2888 p ≤ (0 : Int) + d2177 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2888, d2177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22952 p hg
    simpa only [d2888, d2177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2888, d2177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22941 p hg
    simpa only [d2888, d2177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22954 (p : Pattern) (guard : d5537 p = 1) : d2889 p ≤ (0 : Int) + d2178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2889, d2178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22953 p hg
    simpa only [d2889, d2178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2889, d2178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2889, d2178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22955 (p : Pattern) (guard : d5537 p = 1) : d2890 p ≤ (0 : Int) + d2179 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2890, d2179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22943 p hg
    simpa only [d2890, d2179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2890, d2179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22954 p hg
    simpa only [d2890, d2179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22956 (p : Pattern) (guard : d5537 p = 1) : d2891 p ≤ (0 : Int) + d2180 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2891, d2180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22894 p hg
    simpa only [d2891, d2180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2891, d2180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22955 p hg
    simpa only [d2891, d2180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22957 (p : Pattern) (guard : d5537 p = 1) : d2892 p ≤ (0 : Int) + d2181 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2892, d2181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22685 p hg
    simpa only [d2892, d2181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2892, d2181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22956 p hg
    simpa only [d2892, d2181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22958 (p : Pattern) (guard : d5537 p = 1) : d2893 p ≤ (0 : Int) + d2182 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2893, d2182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22875 p hg
    simpa only [d2893, d2182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2893, d2182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22957 p hg
    simpa only [d2893, d2182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22959 (p : Pattern) (guard : d5537 p = 1) : d2894 p ≤ (0 : Int) + d2183 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2894, d2183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22812 p hg
    simpa only [d2894, d2183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2894, d2183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22958 p hg
    simpa only [d2894, d2183, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
