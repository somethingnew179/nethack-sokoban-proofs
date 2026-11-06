/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons177
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare24920 (p : Pattern) (guard : d5502 p = 1) : d2900 p ≤ (0 : Int) + d2529 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2900, d2529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24913 p hg
    simpa only [d2900, d2529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2900, d2529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24919 p hg
    simpa only [d2900, d2529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24921 (p : Pattern) (guard : d5502 p = 1) : d2901 p ≤ (0 : Int) + d2532 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2901, d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14865 p hg
    simpa only [d2901, d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2901, d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17234 p hg
    simpa only [d2901, d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24922 (p : Pattern) (guard : d5502 p = 1) : d1705 p ≤ (0 : Int) + d2535 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1705, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17116 p hg
    simpa only [d1705, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1705, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1705, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24923 (p : Pattern) (guard : d5502 p = 1) : d2902 p ≤ (0 : Int) + d2536 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2902, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24921 p hg
    simpa only [d2902, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2902, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24922 p hg
    simpa only [d2902, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24924 (p : Pattern) (guard : d5502 p = 1) : d2903 p ≤ (0 : Int) + d2537 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2903, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d2903, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2903, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2903, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24925 (p : Pattern) (guard : d5502 p = 1) : d2904 p ≤ (0 : Int) + d2538 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2904, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24919 p hg
    simpa only [d2904, d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2904, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24924 p hg
    simpa only [d2904, d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24926 (p : Pattern) (guard : d5502 p = 1) : d2905 p ≤ (0 : Int) + d2539 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2905, d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24920 p hg
    simpa only [d2905, d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2905, d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d2905, d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24927 (p : Pattern) (guard : d5502 p = 1) : d2906 p ≤ (0 : Int) + d2518 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2906, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d2906, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2906, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17217 p hg
    simpa only [d2906, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24928 (p : Pattern) (guard : d5502 p = 1) : d1718 p ≤ (0 : Int) + d2543 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1718, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17128 p hg
    simpa only [d1718, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1718, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1718, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24929 (p : Pattern) (guard : d5502 p = 1) : d2907 p ≤ (0 : Int) + d2544 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2907, d2544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d2907, d2544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2907, d2544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24928 p hg
    simpa only [d2907, d2544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24930 (p : Pattern) (guard : d5502 p = 1) : d1725 p ≤ (0 : Int) + d2548 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1725, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17135 p hg
    simpa only [d1725, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1725, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1725, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24931 (p : Pattern) (guard : d5502 p = 1) : d2908 p ≤ (0 : Int) + d2549 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2908, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d2908, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2908, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d2908, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24932 (p : Pattern) (guard : d5502 p = 1) : d2909 p ≤ (0 : Int) + d2550 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2909, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24929 p hg
    simpa only [d2909, d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2909, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24931 p hg
    simpa only [d2909, d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24933 (p : Pattern) (guard : d5502 p = 1) : d1730 p ≤ (0 : Int) + d2553 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1730, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17143 p hg
    simpa only [d1730, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1730, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1730, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24934 (p : Pattern) (guard : d5502 p = 1) : d2910 p ≤ (0 : Int) + d2554 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2910, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d2910, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2910, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24933 p hg
    simpa only [d2910, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24935 (p : Pattern) (guard : d5502 p = 1) : d2911 p ≤ (0 : Int) + d2523 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2911, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14853 p hg
    simpa only [d2911, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2911, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17225 p hg
    simpa only [d2911, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24936 (p : Pattern) (guard : d5502 p = 1) : d2912 p ≤ (0 : Int) + d2555 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2912, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24935 p hg
    simpa only [d2912, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2912, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2912, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24937 (p : Pattern) (guard : d5502 p = 1) : d2913 p ≤ (0 : Int) + d2556 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2913, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d2913, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2913, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d2913, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24938 (p : Pattern) (guard : d5502 p = 1) : d2914 p ≤ (0 : Int) + d2557 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2914, d2557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d2914, d2557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2914, d2557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24937 p hg
    simpa only [d2914, d2557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24939 (p : Pattern) (guard : d5502 p = 1) : d2915 p ≤ (0 : Int) + d2558 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2915, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d2915, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2915, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2915, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24940 (p : Pattern) (guard : d5502 p = 1) : d2916 p ≤ (0 : Int) + d2559 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2916, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24939 p hg
    simpa only [d2916, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2916, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d2916, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24941 (p : Pattern) (guard : d5502 p = 1) : d2917 p ≤ (0 : Int) + d2560 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2917, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24921 p hg
    simpa only [d2917, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2917, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2917, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24942 (p : Pattern) (guard : d5502 p = 1) : d2918 p ≤ (0 : Int) + d2561 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2918, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24941 p hg
    simpa only [d2918, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2918, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2918, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24943 (p : Pattern) (guard : d5502 p = 1) : d2919 p ≤ (0 : Int) + d2562 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2919, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24940 p hg
    simpa only [d2919, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2919, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24942 p hg
    simpa only [d2919, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24944 (p : Pattern) (guard : d5502 p = 1) : d2920 p ≤ (0 : Int) + d2563 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2920, d2563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d2920, d2563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2920, d2563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24943 p hg
    simpa only [d2920, d2563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24945 (p : Pattern) (guard : d5502 p = 1) : d2921 p ≤ (0 : Int) + d2564 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2921, d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24926 p hg
    simpa only [d2921, d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2921, d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d2921, d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24946 (p : Pattern) (guard : d5502 p = 1) : d2895 p ≤ (0 : Int) + d2567 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2895, d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17156 p hg
    simpa only [d2895, d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2895, d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17204 p hg
    simpa only [d2895, d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24947 (p : Pattern) (guard : d5502 p = 1) : d2896 p ≤ (0 : Int) + d2568 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2896, d2568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24946 p hg
    simpa only [d2896, d2568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2896, d2568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24909 p hg
    simpa only [d2896, d2568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24948 (p : Pattern) (guard : d5502 p = 1) : d2922 p ≤ (0 : Int) + d2569 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2922, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14878 p hg
    simpa only [d2922, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2922, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17481 p hg
    simpa only [d2922, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24949 (p : Pattern) (guard : d5502 p = 1) : d1746 p ≤ (0 : Int) + d2572 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1746, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17166 p hg
    simpa only [d1746, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1746, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1746, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24950 (p : Pattern) (guard : d5502 p = 1) : d2923 p ≤ (0 : Int) + d2573 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2923, d2573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24948 p hg
    simpa only [d2923, d2573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2923, d2573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24949 p hg
    simpa only [d2923, d2573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24951 (p : Pattern) (guard : d5502 p = 1) : d2924 p ≤ (0 : Int) + d2574 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2924, d2574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24947 p hg
    simpa only [d2924, d2574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2924, d2574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24950 p hg
    simpa only [d2924, d2574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24952 (p : Pattern) (guard : d5502 p = 1) : d2925 p ≤ (0 : Int) + d2575 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2925, d2575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24918 p hg
    simpa only [d2925, d2575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2925, d2575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d2925, d2575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24953 (p : Pattern) (guard : d5502 p = 1) : d2926 p ≤ (0 : Int) + d2576 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2926, d2576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24951 p hg
    simpa only [d2926, d2576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2926, d2576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24952 p hg
    simpa only [d2926, d2576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24954 (p : Pattern) (guard : d5502 p = 1) : d2927 p ≤ (0 : Int) + d2579 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2927, d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14919 p hg
    simpa only [d2927, d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2927, d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17178 p hg
    simpa only [d2927, d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24955 (p : Pattern) (guard : d5502 p = 1) : d1753 p ≤ (0 : Int) + d2580 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1753, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17178 p hg
    simpa only [d1753, d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1753, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1753, d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24956 (p : Pattern) (guard : d5502 p = 1) : d2928 p ≤ (0 : Int) + d2581 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2928, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24954 p hg
    simpa only [d2928, d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2928, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24955 p hg
    simpa only [d2928, d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24957 (p : Pattern) (guard : d5502 p = 1) : d2929 p ≤ (0 : Int) + d2582 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2929, d2582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24918 p hg
    simpa only [d2929, d2582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2929, d2582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24956 p hg
    simpa only [d2929, d2582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24958 (p : Pattern) (guard : d5502 p = 1) : d2930 p ≤ (0 : Int) + d2583 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2930, d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14889 p hg
    simpa only [d2930, d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2930, d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17143 p hg
    simpa only [d2930, d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24959 (p : Pattern) (guard : d5502 p = 1) : d2931 p ≤ (0 : Int) + d2584 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2931, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24958 p hg
    simpa only [d2931, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2931, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24933 p hg
    simpa only [d2931, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24960 (p : Pattern) (guard : d5502 p = 1) : d2932 p ≤ (0 : Int) + d2585 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2932, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24959 p hg
    simpa only [d2932, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2932, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2932, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24961 (p : Pattern) (guard : d5502 p = 1) : d2933 p ≤ (0 : Int) + d2586 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2933, d2586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24957 p hg
    simpa only [d2933, d2586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2933, d2586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24960 p hg
    simpa only [d2933, d2586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24962 (p : Pattern) (guard : d5502 p = 1) : d2934 p ≤ (0 : Int) + d2587 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2934, d2587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24953 p hg
    simpa only [d2934, d2587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2934, d2587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24961 p hg
    simpa only [d2934, d2587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24963 (p : Pattern) (guard : d5502 p = 1) : d2935 p ≤ (0 : Int) + d2569 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2935, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14878 p hg
    simpa only [d2935, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2935, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17128 p hg
    simpa only [d2935, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24964 (p : Pattern) (guard : d5502 p = 1) : d2936 p ≤ (0 : Int) + d2588 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2936, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24963 p hg
    simpa only [d2936, d2588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2936, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2936, d2588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24965 (p : Pattern) (guard : d5502 p = 1) : d2937 p ≤ (0 : Int) + d2589 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2937, d2589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24931 p hg
    simpa only [d2937, d2589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2937, d2589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24964 p hg
    simpa only [d2937, d2589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24966 (p : Pattern) (guard : d5502 p = 1) : d2938 p ≤ (0 : Int) + d2590 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2938, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d2938, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2938, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24941 p hg
    simpa only [d2938, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24967 (p : Pattern) (guard : d5502 p = 1) : d2939 p ≤ (0 : Int) + d2591 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2939, d2591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24965 p hg
    simpa only [d2939, d2591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2939, d2591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24966 p hg
    simpa only [d2939, d2591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24968 (p : Pattern) (guard : d5502 p = 1) : d2940 p ≤ (0 : Int) + d2592 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2940, d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24954 p hg
    simpa only [d2940, d2592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2940, d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2940, d2592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24969 (p : Pattern) (guard : d5502 p = 1) : d2941 p ≤ (0 : Int) + d2593 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2941, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d2941, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2941, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24968 p hg
    simpa only [d2941, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24970 (p : Pattern) (guard : d5502 p = 1) : d2942 p ≤ (0 : Int) + d2594 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2942, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24958 p hg
    simpa only [d2942, d2594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2942, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2942, d2594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24971 (p : Pattern) (guard : d5502 p = 1) : d2943 p ≤ (0 : Int) + d2595 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2943, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24970 p hg
    simpa only [d2943, d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2943, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2943, d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24972 (p : Pattern) (guard : d5502 p = 1) : d2944 p ≤ (0 : Int) + d2596 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2944, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24969 p hg
    simpa only [d2944, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2944, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24971 p hg
    simpa only [d2944, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24973 (p : Pattern) (guard : d5502 p = 1) : d2945 p ≤ (0 : Int) + d2597 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2945, d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24967 p hg
    simpa only [d2945, d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2945, d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24972 p hg
    simpa only [d2945, d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24974 (p : Pattern) (guard : d5502 p = 1) : d2946 p ≤ (0 : Int) + d2598 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2946, d2598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24962 p hg
    simpa only [d2946, d2598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2946, d2598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24973 p hg
    simpa only [d2946, d2598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24975 (p : Pattern) (guard : d5502 p = 1) : d2947 p ≤ (0 : Int) + d2599 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2947, d2599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24945 p hg
    simpa only [d2947, d2599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2947, d2599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24974 p hg
    simpa only [d2947, d2599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24976 (p : Pattern) (guard : d5502 p = 1) : d2948 p ≤ (0 : Int) + d2518 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2948, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d2948, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2948, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17499 p hg
    simpa only [d2948, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24977 (p : Pattern) (guard : d5502 p = 1) : d1773 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1773, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17204 p hg
    simpa only [d1773, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1773, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1773, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24978 (p : Pattern) (guard : d5502 p = 1) : d2949 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2949, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24976 p hg
    simpa only [d2949, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2949, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24977 p hg
    simpa only [d2949, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24979 (p : Pattern) (guard : d5502 p = 1) : d2950 p ≤ (0 : Int) + d2518 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2950, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d2950, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2950, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17504 p hg
    simpa only [d2950, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24980 (p : Pattern) (guard : d5502 p = 1) : d1782 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1782, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17211 p hg
    simpa only [d1782, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1782, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1782, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24981 (p : Pattern) (guard : d5502 p = 1) : d2951 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2951, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24979 p hg
    simpa only [d2951, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2951, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24980 p hg
    simpa only [d2951, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24982 (p : Pattern) (guard : d5502 p = 1) : d2952 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24978 p hg
    simpa only [d2952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24981 p hg
    simpa only [d2952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24983 (p : Pattern) (guard : d5502 p = 1) : d1789 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1789, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17217 p hg
    simpa only [d1789, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1789, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1789, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24984 (p : Pattern) (guard : d5502 p = 1) : d2953 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2953, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d2953, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2953, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24983 p hg
    simpa only [d2953, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24985 (p : Pattern) (guard : d5502 p = 1) : d1798 p ≤ (0 : Int) + d2602 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1798, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17225 p hg
    simpa only [d1798, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1798, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1798, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24986 (p : Pattern) (guard : d5502 p = 1) : d2954 p ≤ (0 : Int) + d2603 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2954, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24935 p hg
    simpa only [d2954, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2954, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24985 p hg
    simpa only [d2954, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24987 (p : Pattern) (guard : d5502 p = 1) : d2955 p ≤ (0 : Int) + d2604 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2955, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24984 p hg
    simpa only [d2955, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2955, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24986 p hg
    simpa only [d2955, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24988 (p : Pattern) (guard : d5502 p = 1) : d2956 p ≤ (0 : Int) + d2605 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2956, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24982 p hg
    simpa only [d2956, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2956, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24987 p hg
    simpa only [d2956, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24989 (p : Pattern) (guard : d5502 p = 1) : d1804 p ≤ (0 : Int) + d2606 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1804, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17234 p hg
    simpa only [d1804, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1804, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1804, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24990 (p : Pattern) (guard : d5502 p = 1) : d2957 p ≤ (0 : Int) + d2607 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2957, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24921 p hg
    simpa only [d2957, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2957, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24989 p hg
    simpa only [d2957, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24991 (p : Pattern) (guard : d5502 p = 1) : d2958 p ≤ (0 : Int) + d2608 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2958, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24990 p hg
    simpa only [d2958, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2958, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2958, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24992 (p : Pattern) (guard : d5502 p = 1) : d2959 p ≤ (0 : Int) + d2609 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2959, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24987 p hg
    simpa only [d2959, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2959, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24991 p hg
    simpa only [d2959, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24993 (p : Pattern) (guard : d5502 p = 1) : d2960 p ≤ (0 : Int) + d2610 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2960, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24988 p hg
    simpa only [d2960, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2960, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24992 p hg
    simpa only [d2960, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24994 (p : Pattern) (guard : d5502 p = 1) : d2961 p ≤ (0 : Int) + d2611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2961, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24963 p hg
    simpa only [d2961, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2961, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24928 p hg
    simpa only [d2961, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24995 (p : Pattern) (guard : d5502 p = 1) : d2962 p ≤ (0 : Int) + d2612 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2962, d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14883 p hg
    simpa only [d2962, d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2962, d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17135 p hg
    simpa only [d2962, d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24996 (p : Pattern) (guard : d5502 p = 1) : d2963 p ≤ (0 : Int) + d2613 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2963, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24995 p hg
    simpa only [d2963, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2963, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d2963, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24997 (p : Pattern) (guard : d5502 p = 1) : d2964 p ≤ (0 : Int) + d2614 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2964, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24994 p hg
    simpa only [d2964, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2964, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24996 p hg
    simpa only [d2964, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24998 (p : Pattern) (guard : d5502 p = 1) : d2965 p ≤ (0 : Int) + d2615 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2965, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24997 p hg
    simpa only [d2965, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2965, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24960 p hg
    simpa only [d2965, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24999 (p : Pattern) (guard : d5502 p = 1) : d2966 p ≤ (0 : Int) + d2616 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2966, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24998 p hg
    simpa only [d2966, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2966, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2966, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25000 (p : Pattern) (guard : d5502 p = 1) : d2967 p ≤ (0 : Int) + d2617 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2967, d2617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24993 p hg
    simpa only [d2967, d2617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2967, d2617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24999 p hg
    simpa only [d2967, d2617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25001 (p : Pattern) (guard : d5502 p = 1) : d2968 p ≤ (0 : Int) + d2618 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2968, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24981 p hg
    simpa only [d2968, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2968, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24994 p hg
    simpa only [d2968, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25002 (p : Pattern) (guard : d5502 p = 1) : d2969 p ≤ (0 : Int) + d2619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2969, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24986 p hg
    simpa only [d2969, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2969, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24990 p hg
    simpa only [d2969, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25003 (p : Pattern) (guard : d5502 p = 1) : d2970 p ≤ (0 : Int) + d2620 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2970, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25001 p hg
    simpa only [d2970, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2970, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25002 p hg
    simpa only [d2970, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25004 (p : Pattern) (guard : d5502 p = 1) : d2971 p ≤ (0 : Int) + d2621 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2971, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24986 p hg
    simpa only [d2971, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2971, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24956 p hg
    simpa only [d2971, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25005 (p : Pattern) (guard : d5502 p = 1) : d2972 p ≤ (0 : Int) + d2622 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2972, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25004 p hg
    simpa only [d2972, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2972, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24960 p hg
    simpa only [d2972, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25006 (p : Pattern) (guard : d5502 p = 1) : d2973 p ≤ (0 : Int) + d2623 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2973, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25003 p hg
    simpa only [d2973, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2973, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25005 p hg
    simpa only [d2973, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25007 (p : Pattern) (guard : d5502 p = 1) : d2974 p ≤ (0 : Int) + d2624 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2974, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24996 p hg
    simpa only [d2974, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2974, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2974, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25008 (p : Pattern) (guard : d5502 p = 1) : d2975 p ≤ (0 : Int) + d2625 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2975, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25007 p hg
    simpa only [d2975, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2975, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2975, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25009 (p : Pattern) (guard : d5502 p = 1) : d2976 p ≤ (0 : Int) + d2626 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2976, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25008 p hg
    simpa only [d2976, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2976, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2976, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25010 (p : Pattern) (guard : d5502 p = 1) : d2977 p ≤ (0 : Int) + d2627 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2977, d2627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25006 p hg
    simpa only [d2977, d2627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2977, d2627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25009 p hg
    simpa only [d2977, d2627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25011 (p : Pattern) (guard : d5502 p = 1) : d2978 p ≤ (0 : Int) + d2628 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2978, d2628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25000 p hg
    simpa only [d2978, d2628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2978, d2628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25010 p hg
    simpa only [d2978, d2628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25012 (p : Pattern) (guard : d5502 p = 1) : d2979 p ≤ (0 : Int) + d2629 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2979, d2629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24975 p hg
    simpa only [d2979, d2629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2979, d2629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25011 p hg
    simpa only [d2979, d2629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25013 (p : Pattern) (guard : d5502 p = 1) : d2980 p ≤ (0 : Int) + d2630 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2980, d2630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24990 p hg
    simpa only [d2980, d2630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2980, d2630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24959 p hg
    simpa only [d2980, d2630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25014 (p : Pattern) (guard : d5502 p = 1) : d2981 p ≤ (0 : Int) + d2631 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2981, d2631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25013 p hg
    simpa only [d2981, d2631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2981, d2631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24960 p hg
    simpa only [d2981, d2631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25015 (p : Pattern) (guard : d5502 p = 1) : d2982 p ≤ (0 : Int) + d2632 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2982, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24960 p hg
    simpa only [d2982, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2982, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2982, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25016 (p : Pattern) (guard : d5502 p = 1) : d2983 p ≤ (0 : Int) + d2633 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2983, d2633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25014 p hg
    simpa only [d2983, d2633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2983, d2633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25015 p hg
    simpa only [d2983, d2633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25017 (p : Pattern) (guard : d5502 p = 1) : d2984 p ≤ (0 : Int) + d2634 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2984, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25015 p hg
    simpa only [d2984, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2984, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2984, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25018 (p : Pattern) (guard : d5502 p = 1) : d2985 p ≤ (0 : Int) + d2635 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2985, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25016 p hg
    simpa only [d2985, d2635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2985, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25017 p hg
    simpa only [d2985, d2635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25019 (p : Pattern) (guard : d5502 p = 1) : d2986 p ≤ (0 : Int) + d2636 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2986, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25017 p hg
    simpa only [d2986, d2636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2986, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2986, d2636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25020 (p : Pattern) (guard : d5502 p = 1) : d2987 p ≤ (0 : Int) + d2637 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2987, d2637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25018 p hg
    simpa only [d2987, d2637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2987, d2637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25019 p hg
    simpa only [d2987, d2637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25021 (p : Pattern) (guard : d5502 p = 1) : d2988 p ≤ (0 : Int) + d2638 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2988, d2638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25011 p hg
    simpa only [d2988, d2638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2988, d2638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25020 p hg
    simpa only [d2988, d2638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25022 (p : Pattern) (guard : d5502 p = 1) : d2989 p ≤ (0 : Int) + d2639 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2989, d2639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25012 p hg
    simpa only [d2989, d2639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2989, d2639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25021 p hg
    simpa only [d2989, d2639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25023 (p : Pattern) (guard : d5502 p = 1) : d2896 p ≤ (0 : Int) + d2640 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24912 p hg
    simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24915 p hg
    simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25024 (p : Pattern) (guard : d5502 p = 1) : d2900 p ≤ (0 : Int) + d2641 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2900, d2641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25023 p hg
    simpa only [d2900, d2641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2900, d2641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24919 p hg
    simpa only [d2900, d2641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25025 (p : Pattern) (guard : d5502 p = 1) : d2905 p ≤ (0 : Int) + d2642 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2905, d2642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25024 p hg
    simpa only [d2905, d2642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2905, d2642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d2905, d2642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25026 (p : Pattern) (guard : d5502 p = 1) : d2921 p ≤ (0 : Int) + d2643 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2921, d2643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25025 p hg
    simpa only [d2921, d2643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2921, d2643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d2921, d2643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25027 (p : Pattern) (guard : d5502 p = 1) : d2924 p ≤ (0 : Int) + d2644 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2924, d2644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24915 p hg
    simpa only [d2924, d2644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2924, d2644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24950 p hg
    simpa only [d2924, d2644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25028 (p : Pattern) (guard : d5502 p = 1) : d2926 p ≤ (0 : Int) + d2645 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2926, d2645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25027 p hg
    simpa only [d2926, d2645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2926, d2645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24952 p hg
    simpa only [d2926, d2645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25029 (p : Pattern) (guard : d5502 p = 1) : d2934 p ≤ (0 : Int) + d2646 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2934, d2646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25028 p hg
    simpa only [d2934, d2646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2934, d2646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24961 p hg
    simpa only [d2934, d2646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25030 (p : Pattern) (guard : d5502 p = 1) : d2946 p ≤ (0 : Int) + d2647 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2946, d2647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25029 p hg
    simpa only [d2946, d2647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2946, d2647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24973 p hg
    simpa only [d2946, d2647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25031 (p : Pattern) (guard : d5502 p = 1) : d2947 p ≤ (0 : Int) + d2648 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2947, d2648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25026 p hg
    simpa only [d2947, d2648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2947, d2648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25030 p hg
    simpa only [d2947, d2648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25032 (p : Pattern) (guard : d5502 p = 1) : d2979 p ≤ (0 : Int) + d2649 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2979, d2649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25031 p hg
    simpa only [d2979, d2649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2979, d2649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25011 p hg
    simpa only [d2979, d2649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25033 (p : Pattern) (guard : d5502 p = 1) : d2990 p ≤ (0 : Int) + d2650 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2990, d2650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25011 p hg
    simpa only [d2990, d2650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2990, d2650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2990, d2650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25034 (p : Pattern) (guard : d5502 p = 1) : d2991 p ≤ (0 : Int) + d2651 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2991, d2651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25032 p hg
    simpa only [d2991, d2651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2991, d2651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25033 p hg
    simpa only [d2991, d2651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25035 (p : Pattern) (guard : d5502 p = 1) : d2992 p ≤ (0 : Int) + d2652 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2992, d2652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25022 p hg
    simpa only [d2992, d2652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2992, d2652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25034 p hg
    simpa only [d2992, d2652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25036 (p : Pattern) (guard : d5502 p = 1) : d2895 p ≤ (0 : Int) + d2655 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2895, d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17283 p hg
    simpa only [d2895, d2655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2895, d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17204 p hg
    simpa only [d2895, d2655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25037 (p : Pattern) (guard : d5502 p = 1) : d2896 p ≤ (0 : Int) + d2656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2896, d2656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25036 p hg
    simpa only [d2896, d2656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2896, d2656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24909 p hg
    simpa only [d2896, d2656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25038 (p : Pattern) (guard : d5502 p = 1) : d2896 p ≤ (0 : Int) + d2657 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25037 p hg
    simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24915 p hg
    simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25039 (p : Pattern) (guard : d5502 p = 1) : d2900 p ≤ (0 : Int) + d2658 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2900, d2658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25038 p hg
    simpa only [d2900, d2658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2900, d2658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24919 p hg
    simpa only [d2900, d2658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25040 (p : Pattern) (guard : d5502 p = 1) : d2905 p ≤ (0 : Int) + d2659 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2905, d2659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25039 p hg
    simpa only [d2905, d2659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2905, d2659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d2905, d2659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25041 (p : Pattern) (guard : d5502 p = 1) : d2921 p ≤ (0 : Int) + d2660 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2921, d2660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25040 p hg
    simpa only [d2921, d2660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2921, d2660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d2921, d2660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25042 (p : Pattern) (guard : d5502 p = 1) : d2924 p ≤ (0 : Int) + d2661 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2924, d2661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24912 p hg
    simpa only [d2924, d2661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2924, d2661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24950 p hg
    simpa only [d2924, d2661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25043 (p : Pattern) (guard : d5502 p = 1) : d2926 p ≤ (0 : Int) + d2662 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2926, d2662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25042 p hg
    simpa only [d2926, d2662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2926, d2662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24952 p hg
    simpa only [d2926, d2662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25044 (p : Pattern) (guard : d5502 p = 1) : d2934 p ≤ (0 : Int) + d2663 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2934, d2663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25043 p hg
    simpa only [d2934, d2663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2934, d2663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24961 p hg
    simpa only [d2934, d2663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25045 (p : Pattern) (guard : d5502 p = 1) : d2946 p ≤ (0 : Int) + d2664 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2946, d2664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25044 p hg
    simpa only [d2946, d2664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2946, d2664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24973 p hg
    simpa only [d2946, d2664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25046 (p : Pattern) (guard : d5502 p = 1) : d2947 p ≤ (0 : Int) + d2665 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2947, d2665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25041 p hg
    simpa only [d2947, d2665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2947, d2665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25045 p hg
    simpa only [d2947, d2665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25047 (p : Pattern) (guard : d5502 p = 1) : d2979 p ≤ (0 : Int) + d2666 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2979, d2666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25046 p hg
    simpa only [d2979, d2666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2979, d2666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25011 p hg
    simpa only [d2979, d2666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25048 (p : Pattern) (guard : d5502 p = 1) : d2989 p ≤ (0 : Int) + d2667 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2989, d2667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25047 p hg
    simpa only [d2989, d2667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2989, d2667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25021 p hg
    simpa only [d2989, d2667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25049 (p : Pattern) (guard : d5502 p = 1) : d2900 p ≤ (0 : Int) + d2668 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2900, d2668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24915 p hg
    simpa only [d2900, d2668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2900, d2668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24919 p hg
    simpa only [d2900, d2668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25050 (p : Pattern) (guard : d5502 p = 1) : d2905 p ≤ (0 : Int) + d2669 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2905, d2669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25049 p hg
    simpa only [d2905, d2669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2905, d2669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d2905, d2669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25051 (p : Pattern) (guard : d5502 p = 1) : d2921 p ≤ (0 : Int) + d2670 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2921, d2670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25050 p hg
    simpa only [d2921, d2670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2921, d2670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d2921, d2670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25052 (p : Pattern) (guard : d5502 p = 1) : d2947 p ≤ (0 : Int) + d2671 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2947, d2671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25051 p hg
    simpa only [d2947, d2671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2947, d2671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25030 p hg
    simpa only [d2947, d2671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25053 (p : Pattern) (guard : d5502 p = 1) : d2979 p ≤ (0 : Int) + d2672 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2979, d2672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25052 p hg
    simpa only [d2979, d2672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2979, d2672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25011 p hg
    simpa only [d2979, d2672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25054 (p : Pattern) (guard : d5502 p = 1) : d2991 p ≤ (0 : Int) + d2673 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2991, d2673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25053 p hg
    simpa only [d2991, d2673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2991, d2673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25033 p hg
    simpa only [d2991, d2673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25055 (p : Pattern) (guard : d5502 p = 1) : d2992 p ≤ (0 : Int) + d2674 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2992, d2674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25048 p hg
    simpa only [d2992, d2674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2992, d2674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25054 p hg
    simpa only [d2992, d2674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25056 (p : Pattern) (guard : d5502 p = 1) : d2992 p ≤ (0 : Int) + d2675 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25035 p hg
    simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25055 p hg
    simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25057 (p : Pattern) (guard : d5502 p = 1) : d2993 p ≤ (0 : Int) + d2681 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2993, d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17306 p hg
    simpa only [d2993, d2681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2993, d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17390 p hg
    simpa only [d2993, d2681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25058 (p : Pattern) (guard : d5502 p = 1) : d1876 p ≤ (0 : Int) + d2684 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1876, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17313 p hg
    simpa only [d1876, d2684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1876, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1876, d2684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25059 (p : Pattern) (guard : d5502 p = 1) : d2994 p ≤ (0 : Int) + d2685 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2994, d2685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25057 p hg
    simpa only [d2994, d2685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2994, d2685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25058 p hg
    simpa only [d2994, d2685, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
