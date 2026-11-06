/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons105
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare14840 (p : Pattern) (guard : d5503 p = 1) : d14 p ≤ (0 : Int) + d2510 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d5503, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14839 p hg
    simpa only [d5503, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14841 (p : Pattern) (guard : d5503 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare14842 (p : Pattern) (guard : d5503 p = 1) : d15 p ≤ (0 : Int) + d2511 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d15, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14840 p hg
    simpa only [d15, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d15, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d15, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14843 (p : Pattern) (guard : d5503 p = 1) : d16 p ≤ (0 : Int) + d2512 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d16, d2512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14838 p hg
    simpa only [d16, d2512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d16, d2512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14842 p hg
    simpa only [d16, d2512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14844 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d327 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14845 (p : Pattern) (guard : d5502 p = 1) : d14 p ≤ (0 : Int) + d2513 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d5502, d2513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14844 p hg
    simpa only [d5502, d2513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14846 (p : Pattern) (guard : d5503 p = 1) : d14 p ≤ (0 : Int) + d2514 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14845 p hg
    simpa only [d5503, d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14833 p hg
    simpa only [d5503, d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14847 (p : Pattern) (guard : d5503 p = 1) : d14 p ≤ (0 : Int) + d2515 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14846 p hg
    simpa only [d2515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14837 p hg
    simpa only [d2515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14848 (p : Pattern) (guard : d5503 p = 1) : d16 p ≤ (0 : Int) + d2516 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d16, d2516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14847 p hg
    simpa only [d16, d2516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d16, d2516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14842 p hg
    simpa only [d16, d2516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14849 (p : Pattern) (guard : d5503 p = 1) : d16 p ≤ (0 : Int) + d2517 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14843 p hg
    simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14848 p hg
    simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14850 (p : Pattern) (guard : d5503 p = 1) : d14 p ≤ (0 : Int) + d2504 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14833 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14851 (p : Pattern) (guard : d5503 p = 1) : d14 p ≤ (0 : Int) + d2518 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14850 p hg
    simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14837 p hg
    simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14852 (p : Pattern) (guard : d5503 p = 1) : d16 p ≤ (0 : Int) + d2519 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d16, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14851 p hg
    simpa only [d16, d2519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d16, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14842 p hg
    simpa only [d16, d2519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14853 (p : Pattern) (guard : d5502 p = 1) : d18 p ≤ (0 : Int) + d2520 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d5502, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d5502, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14854 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (0 : Int) + d2520 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14855 (p : Pattern) (guard : d5503 p = 1) : d18 p ≤ (0 : Int) + d2520 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14853 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14854 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14856 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (0 : Int) + d2521 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14857 (p : Pattern) (guard : d5503 p = 1) : d18 p ≤ (0 : Int) + d2522 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14853 p hg
    simpa only [d5503, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14856 p hg
    simpa only [d5503, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14858 (p : Pattern) (guard : d5503 p = 1) : d18 p ≤ (0 : Int) + d2523 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14855 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14857 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14859 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (0 : Int) + d2524 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14860 (p : Pattern) (guard : d5503 p = 1) : d18 p ≤ (0 : Int) + d2525 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14853 p hg
    simpa only [d5503, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14859 p hg
    simpa only [d5503, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14861 (p : Pattern) (guard : d5503 p = 1) : d19 p ≤ (0 : Int) + d2526 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d19, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14860 p hg
    simpa only [d19, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d19, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d19, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14862 (p : Pattern) (guard : d5503 p = 1) : d20 p ≤ (0 : Int) + d2527 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d20, d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14858 p hg
    simpa only [d20, d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d20, d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14861 p hg
    simpa only [d20, d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14863 (p : Pattern) (guard : d5503 p = 1) : d21 p ≤ (0 : Int) + d2528 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d21, d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14852 p hg
    simpa only [d21, d2528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d21, d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14862 p hg
    simpa only [d21, d2528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14864 (p : Pattern) (guard : d5503 p = 1) : d22 p ≤ (0 : Int) + d2529 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d22, d2529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14849 p hg
    simpa only [d22, d2529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d22, d2529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14863 p hg
    simpa only [d22, d2529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14865 (p : Pattern) (guard : d5502 p = 1) : d24 p ≤ (0 : Int) + d2530 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d5502, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11467 p hg
    simpa only [d5502, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14866 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (0 : Int) + d2530 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14867 (p : Pattern) (guard : d5503 p = 1) : d24 p ≤ (0 : Int) + d2530 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14865 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14866 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14868 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (0 : Int) + d357 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14869 (p : Pattern) (guard : d5503 p = 1) : d24 p ≤ (0 : Int) + d2531 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14865 p hg
    simpa only [d5503, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14868 p hg
    simpa only [d5503, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14870 (p : Pattern) (guard : d5503 p = 1) : d24 p ≤ (0 : Int) + d2532 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14867 p hg
    simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14869 p hg
    simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14871 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (0 : Int) + d2533 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14872 (p : Pattern) (guard : d5503 p = 1) : d24 p ≤ (0 : Int) + d2534 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14865 p hg
    simpa only [d5503, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14871 p hg
    simpa only [d5503, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14873 (p : Pattern) (guard : d5503 p = 1) : d25 p ≤ (0 : Int) + d2535 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d25, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14872 p hg
    simpa only [d25, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d25, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d25, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14874 (p : Pattern) (guard : d5503 p = 1) : d26 p ≤ (0 : Int) + d2536 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d26, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14870 p hg
    simpa only [d26, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d26, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14873 p hg
    simpa only [d26, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14875 (p : Pattern) (guard : d5503 p = 1) : d27 p ≤ (0 : Int) + d2537 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d27, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14874 p hg
    simpa only [d27, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d27, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d27, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14876 (p : Pattern) (guard : d5503 p = 1) : d28 p ≤ (0 : Int) + d2538 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d28, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14863 p hg
    simpa only [d28, d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d28, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14875 p hg
    simpa only [d28, d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14877 (p : Pattern) (guard : d5503 p = 1) : d29 p ≤ (0 : Int) + d2539 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d29, d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14864 p hg
    simpa only [d29, d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d29, d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14876 p hg
    simpa only [d29, d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14878 (p : Pattern) (guard : d5502 p = 1) : d31 p ≤ (0 : Int) + d2540 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d5502, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d5502, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14879 (p : Pattern) (guard : d0 p = 1) : d31 p ≤ (0 : Int) + d2541 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14880 (p : Pattern) (guard : d5503 p = 1) : d31 p ≤ (0 : Int) + d2542 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14878 p hg
    simpa only [d5503, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14879 p hg
    simpa only [d5503, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14881 (p : Pattern) (guard : d5503 p = 1) : d32 p ≤ (0 : Int) + d2543 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d32, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14880 p hg
    simpa only [d32, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d32, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d32, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14882 (p : Pattern) (guard : d5503 p = 1) : d33 p ≤ (0 : Int) + d2544 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d33, d2544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14851 p hg
    simpa only [d33, d2544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d33, d2544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14881 p hg
    simpa only [d33, d2544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14883 (p : Pattern) (guard : d5502 p = 1) : d35 p ≤ (0 : Int) + d2545 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d5502, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11542 p hg
    simpa only [d5502, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14884 (p : Pattern) (guard : d0 p = 1) : d35 p ≤ (0 : Int) + d2546 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14885 (p : Pattern) (guard : d5503 p = 1) : d35 p ≤ (0 : Int) + d2547 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14883 p hg
    simpa only [d5503, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14884 p hg
    simpa only [d5503, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14886 (p : Pattern) (guard : d5503 p = 1) : d36 p ≤ (0 : Int) + d2548 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d36, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14885 p hg
    simpa only [d36, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d36, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d36, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14887 (p : Pattern) (guard : d5503 p = 1) : d37 p ≤ (0 : Int) + d2549 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d37, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14851 p hg
    simpa only [d37, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d37, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14886 p hg
    simpa only [d37, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14888 (p : Pattern) (guard : d5503 p = 1) : d38 p ≤ (0 : Int) + d2550 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d38, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14882 p hg
    simpa only [d38, d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d38, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14887 p hg
    simpa only [d38, d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14889 (p : Pattern) (guard : d5502 p = 1) : d40 p ≤ (0 : Int) + d2551 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d5502, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11507 p hg
    simpa only [d5502, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14890 (p : Pattern) (guard : d0 p = 1) : d40 p ≤ (0 : Int) + d332 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14891 (p : Pattern) (guard : d5503 p = 1) : d40 p ≤ (0 : Int) + d2552 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14889 p hg
    simpa only [d5503, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14890 p hg
    simpa only [d5503, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14892 (p : Pattern) (guard : d5503 p = 1) : d41 p ≤ (0 : Int) + d2553 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d41, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14891 p hg
    simpa only [d41, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d41, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d41, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14893 (p : Pattern) (guard : d5503 p = 1) : d42 p ≤ (0 : Int) + d2554 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d42, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14851 p hg
    simpa only [d42, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d42, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14892 p hg
    simpa only [d42, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14894 (p : Pattern) (guard : d5503 p = 1) : d43 p ≤ (0 : Int) + d2555 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d43, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14858 p hg
    simpa only [d43, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d43, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d43, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14895 (p : Pattern) (guard : d5503 p = 1) : d44 p ≤ (0 : Int) + d2556 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d44, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14893 p hg
    simpa only [d44, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d44, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14894 p hg
    simpa only [d44, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14896 (p : Pattern) (guard : d5503 p = 1) : d45 p ≤ (0 : Int) + d2557 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d45, d2557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14888 p hg
    simpa only [d45, d2557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d45, d2557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14895 p hg
    simpa only [d45, d2557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14897 (p : Pattern) (guard : d5503 p = 1) : d46 p ≤ (0 : Int) + d2558 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d46, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14851 p hg
    simpa only [d46, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d46, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d46, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14898 (p : Pattern) (guard : d5503 p = 1) : d47 p ≤ (0 : Int) + d2559 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d47, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14897 p hg
    simpa only [d47, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d47, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14894 p hg
    simpa only [d47, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14899 (p : Pattern) (guard : d5503 p = 1) : d48 p ≤ (0 : Int) + d2560 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d48, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14870 p hg
    simpa only [d48, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d48, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d48, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14900 (p : Pattern) (guard : d5503 p = 1) : d49 p ≤ (0 : Int) + d2561 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d49, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14899 p hg
    simpa only [d49, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d49, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d49, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14901 (p : Pattern) (guard : d5503 p = 1) : d50 p ≤ (0 : Int) + d2562 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d50, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14898 p hg
    simpa only [d50, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d50, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14900 p hg
    simpa only [d50, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14902 (p : Pattern) (guard : d5503 p = 1) : d51 p ≤ (0 : Int) + d2563 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d51, d2563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14896 p hg
    simpa only [d51, d2563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d51, d2563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14901 p hg
    simpa only [d51, d2563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14903 (p : Pattern) (guard : d5503 p = 1) : d52 p ≤ (0 : Int) + d2564 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d52, d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14877 p hg
    simpa only [d52, d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d52, d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14902 p hg
    simpa only [d52, d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14904 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d329 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14905 (p : Pattern) (guard : d5502 p = 1) : d14 p ≤ (0 : Int) + d2565 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d5502, d2565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14904 p hg
    simpa only [d5502, d2565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14906 (p : Pattern) (guard : d5503 p = 1) : d14 p ≤ (0 : Int) + d2566 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14905 p hg
    simpa only [d5503, d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14833 p hg
    simpa only [d5503, d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14907 (p : Pattern) (guard : d5503 p = 1) : d14 p ≤ (0 : Int) + d2567 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14906 p hg
    simpa only [d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14837 p hg
    simpa only [d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14908 (p : Pattern) (guard : d5503 p = 1) : d16 p ≤ (0 : Int) + d2568 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d16, d2568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14907 p hg
    simpa only [d16, d2568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d16, d2568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14842 p hg
    simpa only [d16, d2568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14909 (p : Pattern) (guard : d0 p = 1) : d31 p ≤ (0 : Int) + d2540 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14910 (p : Pattern) (guard : d5503 p = 1) : d31 p ≤ (0 : Int) + d2540 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14878 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14909 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14911 (p : Pattern) (guard : d5503 p = 1) : d31 p ≤ (0 : Int) + d2569 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14910 p hg
    simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14880 p hg
    simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14912 (p : Pattern) (guard : d0 p = 1) : d31 p ≤ (0 : Int) + d2570 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14913 (p : Pattern) (guard : d5503 p = 1) : d31 p ≤ (0 : Int) + d2571 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14878 p hg
    simpa only [d5503, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14912 p hg
    simpa only [d5503, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14914 (p : Pattern) (guard : d5503 p = 1) : d32 p ≤ (0 : Int) + d2572 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d32, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14913 p hg
    simpa only [d32, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d32, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d32, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14915 (p : Pattern) (guard : d5503 p = 1) : d53 p ≤ (0 : Int) + d2573 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d53, d2573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14911 p hg
    simpa only [d53, d2573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d53, d2573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14914 p hg
    simpa only [d53, d2573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14916 (p : Pattern) (guard : d5503 p = 1) : d54 p ≤ (0 : Int) + d2574 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d54, d2574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14908 p hg
    simpa only [d54, d2574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d54, d2574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14915 p hg
    simpa only [d54, d2574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14917 (p : Pattern) (guard : d5503 p = 1) : d55 p ≤ (0 : Int) + d2575 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d55, d2575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14862 p hg
    simpa only [d55, d2575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d55, d2575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14874 p hg
    simpa only [d55, d2575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14918 (p : Pattern) (guard : d5503 p = 1) : d56 p ≤ (0 : Int) + d2576 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d56, d2576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14916 p hg
    simpa only [d56, d2576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d56, d2576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14917 p hg
    simpa only [d56, d2576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14919 (p : Pattern) (guard : d5502 p = 1) : d58 p ≤ (0 : Int) + d2577 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d5502, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11502 p hg
    simpa only [d5502, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14920 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (0 : Int) + d2577 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14921 (p : Pattern) (guard : d5503 p = 1) : d58 p ≤ (0 : Int) + d2577 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14919 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14920 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14922 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (0 : Int) + d330 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14923 (p : Pattern) (guard : d5503 p = 1) : d58 p ≤ (0 : Int) + d2578 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14919 p hg
    simpa only [d5503, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14922 p hg
    simpa only [d5503, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14924 (p : Pattern) (guard : d5503 p = 1) : d58 p ≤ (0 : Int) + d2579 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14921 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14923 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14925 (p : Pattern) (guard : d5503 p = 1) : d59 p ≤ (0 : Int) + d2580 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d59, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14923 p hg
    simpa only [d59, d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d59, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d59, d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14926 (p : Pattern) (guard : d5503 p = 1) : d60 p ≤ (0 : Int) + d2581 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d60, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14924 p hg
    simpa only [d60, d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d60, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14925 p hg
    simpa only [d60, d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14927 (p : Pattern) (guard : d5503 p = 1) : d61 p ≤ (0 : Int) + d2582 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d61, d2582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14862 p hg
    simpa only [d61, d2582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d61, d2582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14926 p hg
    simpa only [d61, d2582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14928 (p : Pattern) (guard : d0 p = 1) : d40 p ≤ (0 : Int) + d2551 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14929 (p : Pattern) (guard : d5503 p = 1) : d40 p ≤ (0 : Int) + d2551 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14889 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14928 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14930 (p : Pattern) (guard : d5503 p = 1) : d40 p ≤ (0 : Int) + d2583 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14929 p hg
    simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14891 p hg
    simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14931 (p : Pattern) (guard : d5503 p = 1) : d62 p ≤ (0 : Int) + d2584 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d62, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14930 p hg
    simpa only [d62, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d62, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14892 p hg
    simpa only [d62, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14932 (p : Pattern) (guard : d5503 p = 1) : d63 p ≤ (0 : Int) + d2585 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d63, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14931 p hg
    simpa only [d63, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d63, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d63, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14933 (p : Pattern) (guard : d5503 p = 1) : d64 p ≤ (0 : Int) + d2586 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d64, d2586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14927 p hg
    simpa only [d64, d2586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d64, d2586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14932 p hg
    simpa only [d64, d2586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14934 (p : Pattern) (guard : d5503 p = 1) : d65 p ≤ (0 : Int) + d2587 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d65, d2587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14918 p hg
    simpa only [d65, d2587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d65, d2587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14933 p hg
    simpa only [d65, d2587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14935 (p : Pattern) (guard : d5503 p = 1) : d66 p ≤ (0 : Int) + d2588 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d66, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14911 p hg
    simpa only [d66, d2588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d66, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d66, d2588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14936 (p : Pattern) (guard : d5503 p = 1) : d67 p ≤ (0 : Int) + d2589 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d67, d2589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14887 p hg
    simpa only [d67, d2589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d67, d2589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14935 p hg
    simpa only [d67, d2589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14937 (p : Pattern) (guard : d5503 p = 1) : d68 p ≤ (0 : Int) + d2590 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d68, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14894 p hg
    simpa only [d68, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d68, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14899 p hg
    simpa only [d68, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14938 (p : Pattern) (guard : d5503 p = 1) : d69 p ≤ (0 : Int) + d2591 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d69, d2591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14936 p hg
    simpa only [d69, d2591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d69, d2591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14937 p hg
    simpa only [d69, d2591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14939 (p : Pattern) (guard : d5503 p = 1) : d70 p ≤ (0 : Int) + d2592 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d70, d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14924 p hg
    simpa only [d70, d2592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d70, d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d70, d2592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14940 (p : Pattern) (guard : d5503 p = 1) : d71 p ≤ (0 : Int) + d2593 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d71, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14894 p hg
    simpa only [d71, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d71, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14939 p hg
    simpa only [d71, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14941 (p : Pattern) (guard : d5503 p = 1) : d72 p ≤ (0 : Int) + d2594 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d72, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14930 p hg
    simpa only [d72, d2594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d72, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d72, d2594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14942 (p : Pattern) (guard : d5503 p = 1) : d73 p ≤ (0 : Int) + d2595 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d73, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14941 p hg
    simpa only [d73, d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d73, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d73, d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14943 (p : Pattern) (guard : d5503 p = 1) : d74 p ≤ (0 : Int) + d2596 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d74, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14940 p hg
    simpa only [d74, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d74, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14942 p hg
    simpa only [d74, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14944 (p : Pattern) (guard : d5503 p = 1) : d75 p ≤ (0 : Int) + d2597 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d75, d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14938 p hg
    simpa only [d75, d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d75, d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14943 p hg
    simpa only [d75, d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14945 (p : Pattern) (guard : d5503 p = 1) : d76 p ≤ (0 : Int) + d2598 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d76, d2598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14934 p hg
    simpa only [d76, d2598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d76, d2598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14944 p hg
    simpa only [d76, d2598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14946 (p : Pattern) (guard : d5503 p = 1) : d77 p ≤ (0 : Int) + d2599 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d77, d2599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14903 p hg
    simpa only [d77, d2599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d77, d2599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14945 p hg
    simpa only [d77, d2599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14947 (p : Pattern) (guard : d5503 p = 1) : d15 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d15, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14837 p hg
    simpa only [d15, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d15, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d15, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14948 (p : Pattern) (guard : d5503 p = 1) : d16 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d16, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14851 p hg
    simpa only [d16, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d16, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14947 p hg
    simpa only [d16, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14949 (p : Pattern) (guard : d5503 p = 1) : d19 p ≤ (0 : Int) + d2602 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d19, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14857 p hg
    simpa only [d19, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d19, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d19, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14950 (p : Pattern) (guard : d5503 p = 1) : d20 p ≤ (0 : Int) + d2603 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d20, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14858 p hg
    simpa only [d20, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d20, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14949 p hg
    simpa only [d20, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14951 (p : Pattern) (guard : d5503 p = 1) : d21 p ≤ (0 : Int) + d2604 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d21, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14948 p hg
    simpa only [d21, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d21, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14950 p hg
    simpa only [d21, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14952 (p : Pattern) (guard : d5503 p = 1) : d22 p ≤ (0 : Int) + d2605 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d22, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14948 p hg
    simpa only [d22, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d22, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14951 p hg
    simpa only [d22, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14953 (p : Pattern) (guard : d5503 p = 1) : d25 p ≤ (0 : Int) + d2606 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d25, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14869 p hg
    simpa only [d25, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d25, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d25, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14954 (p : Pattern) (guard : d5503 p = 1) : d26 p ≤ (0 : Int) + d2607 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d26, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14870 p hg
    simpa only [d26, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d26, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14953 p hg
    simpa only [d26, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14955 (p : Pattern) (guard : d5503 p = 1) : d27 p ≤ (0 : Int) + d2608 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d27, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14954 p hg
    simpa only [d27, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d27, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d27, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14956 (p : Pattern) (guard : d5503 p = 1) : d28 p ≤ (0 : Int) + d2609 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d28, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14951 p hg
    simpa only [d28, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d28, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14955 p hg
    simpa only [d28, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14957 (p : Pattern) (guard : d5503 p = 1) : d29 p ≤ (0 : Int) + d2610 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d29, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14952 p hg
    simpa only [d29, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d29, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14956 p hg
    simpa only [d29, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14958 (p : Pattern) (guard : d5503 p = 1) : d53 p ≤ (0 : Int) + d2611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d53, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14911 p hg
    simpa only [d53, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d53, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14881 p hg
    simpa only [d53, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14959 (p : Pattern) (guard : d0 p = 1) : d35 p ≤ (0 : Int) + d2545 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14960 (p : Pattern) (guard : d5503 p = 1) : d35 p ≤ (0 : Int) + d2545 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14883 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14959 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14961 (p : Pattern) (guard : d5503 p = 1) : d35 p ≤ (0 : Int) + d2612 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14960 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14885 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14962 (p : Pattern) (guard : d5503 p = 1) : d78 p ≤ (0 : Int) + d2613 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d78, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14961 p hg
    simpa only [d78, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d78, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14886 p hg
    simpa only [d78, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14963 (p : Pattern) (guard : d5503 p = 1) : d79 p ≤ (0 : Int) + d2614 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d79, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14958 p hg
    simpa only [d79, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d79, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14962 p hg
    simpa only [d79, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14964 (p : Pattern) (guard : d5503 p = 1) : d80 p ≤ (0 : Int) + d2615 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d80, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14963 p hg
    simpa only [d80, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d80, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14932 p hg
    simpa only [d80, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14965 (p : Pattern) (guard : d5503 p = 1) : d81 p ≤ (0 : Int) + d2616 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d81, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14964 p hg
    simpa only [d81, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d81, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d81, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14966 (p : Pattern) (guard : d5503 p = 1) : d82 p ≤ (0 : Int) + d2617 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d82, d2617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14957 p hg
    simpa only [d82, d2617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d82, d2617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14965 p hg
    simpa only [d82, d2617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14967 (p : Pattern) (guard : d5503 p = 1) : d54 p ≤ (0 : Int) + d2618 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d54, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14948 p hg
    simpa only [d54, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d54, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14958 p hg
    simpa only [d54, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14968 (p : Pattern) (guard : d5503 p = 1) : d55 p ≤ (0 : Int) + d2619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d55, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14950 p hg
    simpa only [d55, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d55, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14954 p hg
    simpa only [d55, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14969 (p : Pattern) (guard : d5503 p = 1) : d56 p ≤ (0 : Int) + d2620 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d56, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14967 p hg
    simpa only [d56, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d56, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14968 p hg
    simpa only [d56, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14970 (p : Pattern) (guard : d5503 p = 1) : d61 p ≤ (0 : Int) + d2621 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d61, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14950 p hg
    simpa only [d61, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d61, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14926 p hg
    simpa only [d61, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14971 (p : Pattern) (guard : d5503 p = 1) : d64 p ≤ (0 : Int) + d2622 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d64, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14970 p hg
    simpa only [d64, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d64, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14932 p hg
    simpa only [d64, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14972 (p : Pattern) (guard : d5503 p = 1) : d65 p ≤ (0 : Int) + d2623 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d65, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14969 p hg
    simpa only [d65, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d65, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14971 p hg
    simpa only [d65, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14973 (p : Pattern) (guard : d5503 p = 1) : d83 p ≤ (0 : Int) + d2624 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d83, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14962 p hg
    simpa only [d83, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d83, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d83, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14974 (p : Pattern) (guard : d5503 p = 1) : d84 p ≤ (0 : Int) + d2625 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d84, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14973 p hg
    simpa only [d84, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d84, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d84, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14975 (p : Pattern) (guard : d5503 p = 1) : d85 p ≤ (0 : Int) + d2626 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d85, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14974 p hg
    simpa only [d85, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d85, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d85, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14976 (p : Pattern) (guard : d5503 p = 1) : d86 p ≤ (0 : Int) + d2627 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d86, d2627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14972 p hg
    simpa only [d86, d2627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d86, d2627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14975 p hg
    simpa only [d86, d2627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14977 (p : Pattern) (guard : d5503 p = 1) : d87 p ≤ (0 : Int) + d2628 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d87, d2628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14966 p hg
    simpa only [d87, d2628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d87, d2628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14976 p hg
    simpa only [d87, d2628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14978 (p : Pattern) (guard : d5503 p = 1) : d88 p ≤ (0 : Int) + d2629 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d88, d2629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14946 p hg
    simpa only [d88, d2629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d88, d2629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14977 p hg
    simpa only [d88, d2629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14979 (p : Pattern) (guard : d5503 p = 1) : d89 p ≤ (0 : Int) + d2630 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d89, d2630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14954 p hg
    simpa only [d89, d2630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d89, d2630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14931 p hg
    simpa only [d89, d2630, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
