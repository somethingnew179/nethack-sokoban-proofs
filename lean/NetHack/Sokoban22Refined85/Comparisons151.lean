/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare21140 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1711 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21141 (p : Pattern) (guard : d5502 p = 1) : d2540 p ≤ (0 : Int) + d1712 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2540, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d5502, d2540, d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2540, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21140 p hg
    simpa only [d5502, d2540, d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21142 (p : Pattern) (guard : d5502 p = 1) : d2541 p ≤ (0 : Int) + d1716 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2541, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17125 p hg
    simpa only [d5502, d2541, d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2541, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20576 p hg
    simpa only [d5502, d2541, d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21143 (p : Pattern) (guard : d5502 p = 1) : d2542 p ≤ (0 : Int) + d1717 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2542, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21141 p hg
    simpa only [d2542, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2542, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21142 p hg
    simpa only [d2542, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21144 (p : Pattern) (guard : d5502 p = 1) : d2543 p ≤ (0 : Int) + d1718 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2543, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21143 p hg
    simpa only [d2543, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2543, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2543, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21145 (p : Pattern) (guard : d5502 p = 1) : d2544 p ≤ (0 : Int) + d2907 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2544, d2907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21139 p hg
    simpa only [d2544, d2907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2544, d2907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21144 p hg
    simpa only [d2544, d2907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21146 (p : Pattern) (guard : d5502 p = 1) : d2545 p ≤ (0 : Int) + d1720 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2545, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d5502, d2545, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2545, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20581 p hg
    simpa only [d5502, d2545, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21147 (p : Pattern) (guard : d5502 p = 1) : d2546 p ≤ (0 : Int) + d1723 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2546, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17133 p hg
    simpa only [d5502, d2546, d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2546, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20581 p hg
    simpa only [d5502, d2546, d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21148 (p : Pattern) (guard : d5502 p = 1) : d2547 p ≤ (0 : Int) + d1724 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2547, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21146 p hg
    simpa only [d2547, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2547, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21147 p hg
    simpa only [d2547, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21149 (p : Pattern) (guard : d5502 p = 1) : d2548 p ≤ (0 : Int) + d1725 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2548, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21148 p hg
    simpa only [d2548, d1725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2548, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2548, d1725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21150 (p : Pattern) (guard : d5502 p = 1) : d2549 p ≤ (0 : Int) + d2908 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2549, d2908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21139 p hg
    simpa only [d2549, d2908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2549, d2908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21149 p hg
    simpa only [d2549, d2908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21151 (p : Pattern) (guard : d5502 p = 1) : d2550 p ≤ (0 : Int) + d2909 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2550, d2909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21145 p hg
    simpa only [d2550, d2909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2550, d2909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21150 p hg
    simpa only [d2550, d2909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21152 (p : Pattern) (guard : d5502 p = 1) : d2551 p ≤ (0 : Int) + d1728 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2551, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d5502, d2551, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2551, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19457 p hg
    simpa only [d5502, d2551, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21153 (p : Pattern) (guard : d5502 p = 1) : d332 p ≤ (0 : Int) + d327 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17141 p hg
    simpa only [d5502, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19457 p hg
    simpa only [d5502, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21154 (p : Pattern) (guard : d5502 p = 1) : d2552 p ≤ (0 : Int) + d1729 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2552, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21152 p hg
    simpa only [d2552, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2552, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21153 p hg
    simpa only [d2552, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21155 (p : Pattern) (guard : d5502 p = 1) : d2553 p ≤ (0 : Int) + d1730 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2553, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21154 p hg
    simpa only [d2553, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2553, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2553, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21156 (p : Pattern) (guard : d5502 p = 1) : d2554 p ≤ (0 : Int) + d2910 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2554, d2910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21139 p hg
    simpa only [d2554, d2910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2554, d2910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21155 p hg
    simpa only [d2554, d2910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21157 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1792 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21158 (p : Pattern) (guard : d5502 p = 1) : d2520 p ≤ (0 : Int) + d1793 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2520, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d5502, d2520, d1793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2520, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21157 p hg
    simpa only [d5502, d2520, d1793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21159 (p : Pattern) (guard : d5502 p = 1) : d2521 p ≤ (0 : Int) + d1796 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2521, d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17222 p hg
    simpa only [d5502, d2521, d1796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2521, d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20598 p hg
    simpa only [d5502, d2521, d1796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21160 (p : Pattern) (guard : d5502 p = 1) : d2522 p ≤ (0 : Int) + d1797 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2522, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21158 p hg
    simpa only [d2522, d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2522, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21159 p hg
    simpa only [d2522, d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21161 (p : Pattern) (guard : d5502 p = 1) : d2523 p ≤ (0 : Int) + d2911 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2523, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21109 p hg
    simpa only [d2523, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2523, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21160 p hg
    simpa only [d2523, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21162 (p : Pattern) (guard : d5502 p = 1) : d2555 p ≤ (0 : Int) + d2912 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2555, d2912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21161 p hg
    simpa only [d2555, d2912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2555, d2912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2555, d2912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21163 (p : Pattern) (guard : d5502 p = 1) : d2556 p ≤ (0 : Int) + d2913 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2556, d2913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21156 p hg
    simpa only [d2556, d2913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2556, d2913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21162 p hg
    simpa only [d2556, d2913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21164 (p : Pattern) (guard : d5502 p = 1) : d2557 p ≤ (0 : Int) + d2914 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2557, d2914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21151 p hg
    simpa only [d2557, d2914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2557, d2914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21163 p hg
    simpa only [d2557, d2914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21165 (p : Pattern) (guard : d5502 p = 1) : d2558 p ≤ (0 : Int) + d2915 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2558, d2915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21139 p hg
    simpa only [d2558, d2915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2558, d2915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2558, d2915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21166 (p : Pattern) (guard : d5502 p = 1) : d2559 p ≤ (0 : Int) + d2916 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2559, d2916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21165 p hg
    simpa only [d2559, d2916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2559, d2916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21162 p hg
    simpa only [d2559, d2916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21167 (p : Pattern) (guard : d5502 p = 1) : d2560 p ≤ (0 : Int) + d2917 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2560, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21125 p hg
    simpa only [d2560, d2917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2560, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2560, d2917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21168 (p : Pattern) (guard : d5502 p = 1) : d2561 p ≤ (0 : Int) + d2918 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2561, d2918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21167 p hg
    simpa only [d2561, d2918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2561, d2918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2561, d2918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21169 (p : Pattern) (guard : d5502 p = 1) : d2562 p ≤ (0 : Int) + d2919 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2562, d2919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21166 p hg
    simpa only [d2562, d2919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2562, d2919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21168 p hg
    simpa only [d2562, d2919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21170 (p : Pattern) (guard : d5502 p = 1) : d2563 p ≤ (0 : Int) + d2920 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2563, d2920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21164 p hg
    simpa only [d2563, d2920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2563, d2920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21169 p hg
    simpa only [d2563, d2920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21171 (p : Pattern) (guard : d5502 p = 1) : d2564 p ≤ (0 : Int) + d2921 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2564, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21133 p hg
    simpa only [d2564, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2564, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21170 p hg
    simpa only [d2564, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21172 (p : Pattern) (guard : d0 p = 1) : d329 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21173 (p : Pattern) (guard : d5502 p = 1) : d2565 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d5502, d2565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21172 p hg
    simpa only [d5502, d2565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21174 (p : Pattern) (guard : d5502 p = 1) : d2566 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21173 p hg
    simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21175 (p : Pattern) (guard : d5502 p = 1) : d2567 p ≤ (0 : Int) + d2895 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2567, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21174 p hg
    simpa only [d2567, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2567, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21093 p hg
    simpa only [d2567, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21176 (p : Pattern) (guard : d5502 p = 1) : d2568 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2568, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21175 p hg
    simpa only [d2568, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2568, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21099 p hg
    simpa only [d2568, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21177 (p : Pattern) (guard : d5502 p = 1) : d2540 p ≤ (0 : Int) + d31 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d5502, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5677 p hg
    simpa only [d5502, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21178 (p : Pattern) (guard : d5502 p = 1) : d2540 p ≤ (0 : Int) + d2029 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2540, d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d5502, d2540, d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2540, d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19446 p hg
    simpa only [d5502, d2540, d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21179 (p : Pattern) (guard : d5502 p = 1) : d2541 p ≤ (0 : Int) + d1714 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17125 p hg
    simpa only [d5502, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19446 p hg
    simpa only [d5502, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21180 (p : Pattern) (guard : d5502 p = 1) : d2542 p ≤ (0 : Int) + d2030 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2542, d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21178 p hg
    simpa only [d2542, d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2542, d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21179 p hg
    simpa only [d2542, d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21181 (p : Pattern) (guard : d5502 p = 1) : d2569 p ≤ (0 : Int) + d2922 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2569, d2922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21177 p hg
    simpa only [d2569, d2922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2569, d2922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21180 p hg
    simpa only [d2569, d2922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21182 (p : Pattern) (guard : d5502 p = 1) : d2540 p ≤ (0 : Int) + d1744 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2540, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d5502, d2540, d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2540, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19476 p hg
    simpa only [d5502, d2540, d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21183 (p : Pattern) (guard : d5502 p = 1) : d2570 p ≤ (0 : Int) + d1743 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17164 p hg
    simpa only [d5502, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19476 p hg
    simpa only [d5502, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21184 (p : Pattern) (guard : d5502 p = 1) : d2571 p ≤ (0 : Int) + d1745 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2571, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21182 p hg
    simpa only [d2571, d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2571, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21183 p hg
    simpa only [d2571, d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21185 (p : Pattern) (guard : d5502 p = 1) : d2572 p ≤ (0 : Int) + d1746 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2572, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21184 p hg
    simpa only [d2572, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2572, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2572, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21186 (p : Pattern) (guard : d5502 p = 1) : d2573 p ≤ (0 : Int) + d2923 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2573, d2923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21181 p hg
    simpa only [d2573, d2923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2573, d2923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21185 p hg
    simpa only [d2573, d2923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21187 (p : Pattern) (guard : d5502 p = 1) : d2574 p ≤ (0 : Int) + d2924 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2574, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21176 p hg
    simpa only [d2574, d2924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2574, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21186 p hg
    simpa only [d2574, d2924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21188 (p : Pattern) (guard : d5502 p = 1) : d2575 p ≤ (0 : Int) + d2925 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2575, d2925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21118 p hg
    simpa only [d2575, d2925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2575, d2925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21130 p hg
    simpa only [d2575, d2925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21189 (p : Pattern) (guard : d5502 p = 1) : d2576 p ≤ (0 : Int) + d2926 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2576, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21187 p hg
    simpa only [d2576, d2926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2576, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21188 p hg
    simpa only [d2576, d2926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21190 (p : Pattern) (guard : d5502 p = 1) : d2577 p ≤ (0 : Int) + d58 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d5502, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5684 p hg
    simpa only [d5502, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21191 (p : Pattern) (guard : d5502 p = 1) : d2577 p ≤ (0 : Int) + d1751 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2577, d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d5502, d2577, d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2577, d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19485 p hg
    simpa only [d5502, d2577, d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21192 (p : Pattern) (guard : d5502 p = 1) : d330 p ≤ (0 : Int) + d329 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17176 p hg
    simpa only [d5502, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19485 p hg
    simpa only [d5502, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21193 (p : Pattern) (guard : d5502 p = 1) : d2578 p ≤ (0 : Int) + d1752 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2578, d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21191 p hg
    simpa only [d2578, d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2578, d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21192 p hg
    simpa only [d2578, d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21194 (p : Pattern) (guard : d5502 p = 1) : d2579 p ≤ (0 : Int) + d2927 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2579, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21190 p hg
    simpa only [d2579, d2927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2579, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21193 p hg
    simpa only [d2579, d2927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21195 (p : Pattern) (guard : d5502 p = 1) : d2580 p ≤ (0 : Int) + d1753 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2580, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21193 p hg
    simpa only [d2580, d1753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2580, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2580, d1753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21196 (p : Pattern) (guard : d5502 p = 1) : d2581 p ≤ (0 : Int) + d2928 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2581, d2928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21194 p hg
    simpa only [d2581, d2928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2581, d2928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21195 p hg
    simpa only [d2581, d2928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21197 (p : Pattern) (guard : d5502 p = 1) : d2582 p ≤ (0 : Int) + d2929 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2582, d2929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21118 p hg
    simpa only [d2582, d2929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2582, d2929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21196 p hg
    simpa only [d2582, d2929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21198 (p : Pattern) (guard : d5502 p = 1) : d2551 p ≤ (0 : Int) + d40 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d5502, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5689 p hg
    simpa only [d5502, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21199 (p : Pattern) (guard : d5502 p = 1) : d2583 p ≤ (0 : Int) + d2930 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2583, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21198 p hg
    simpa only [d2583, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2583, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21154 p hg
    simpa only [d2583, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21200 (p : Pattern) (guard : d5502 p = 1) : d2584 p ≤ (0 : Int) + d2931 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2584, d2931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21199 p hg
    simpa only [d2584, d2931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2584, d2931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21155 p hg
    simpa only [d2584, d2931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21201 (p : Pattern) (guard : d5502 p = 1) : d2585 p ≤ (0 : Int) + d2932 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2585, d2932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21200 p hg
    simpa only [d2585, d2932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2585, d2932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2585, d2932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21202 (p : Pattern) (guard : d5502 p = 1) : d2586 p ≤ (0 : Int) + d2933 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2586, d2933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21197 p hg
    simpa only [d2586, d2933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2586, d2933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21201 p hg
    simpa only [d2586, d2933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21203 (p : Pattern) (guard : d5502 p = 1) : d2587 p ≤ (0 : Int) + d2934 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2587, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21189 p hg
    simpa only [d2587, d2934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2587, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21202 p hg
    simpa only [d2587, d2934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21204 (p : Pattern) (guard : d5502 p = 1) : d2569 p ≤ (0 : Int) + d2935 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2569, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21177 p hg
    simpa only [d2569, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2569, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21143 p hg
    simpa only [d2569, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21205 (p : Pattern) (guard : d5502 p = 1) : d2588 p ≤ (0 : Int) + d2936 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2588, d2936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21204 p hg
    simpa only [d2588, d2936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2588, d2936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2588, d2936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21206 (p : Pattern) (guard : d5502 p = 1) : d2589 p ≤ (0 : Int) + d2937 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2589, d2937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21150 p hg
    simpa only [d2589, d2937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2589, d2937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21205 p hg
    simpa only [d2589, d2937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21207 (p : Pattern) (guard : d5502 p = 1) : d2590 p ≤ (0 : Int) + d2938 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2590, d2938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21162 p hg
    simpa only [d2590, d2938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2590, d2938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21167 p hg
    simpa only [d2590, d2938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21208 (p : Pattern) (guard : d5502 p = 1) : d2591 p ≤ (0 : Int) + d2939 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2591, d2939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21206 p hg
    simpa only [d2591, d2939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2591, d2939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21207 p hg
    simpa only [d2591, d2939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21209 (p : Pattern) (guard : d5502 p = 1) : d2592 p ≤ (0 : Int) + d2940 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2592, d2940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21194 p hg
    simpa only [d2592, d2940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2592, d2940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2592, d2940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21210 (p : Pattern) (guard : d5502 p = 1) : d2593 p ≤ (0 : Int) + d2941 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2593, d2941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21162 p hg
    simpa only [d2593, d2941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2593, d2941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21209 p hg
    simpa only [d2593, d2941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21211 (p : Pattern) (guard : d5502 p = 1) : d2594 p ≤ (0 : Int) + d2942 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2594, d2942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21199 p hg
    simpa only [d2594, d2942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2594, d2942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2594, d2942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21212 (p : Pattern) (guard : d5502 p = 1) : d2595 p ≤ (0 : Int) + d2943 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2595, d2943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21211 p hg
    simpa only [d2595, d2943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2595, d2943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2595, d2943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21213 (p : Pattern) (guard : d5502 p = 1) : d2596 p ≤ (0 : Int) + d2944 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2596, d2944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21210 p hg
    simpa only [d2596, d2944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2596, d2944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21212 p hg
    simpa only [d2596, d2944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21214 (p : Pattern) (guard : d5502 p = 1) : d2597 p ≤ (0 : Int) + d2945 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2597, d2945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21208 p hg
    simpa only [d2597, d2945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2597, d2945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21213 p hg
    simpa only [d2597, d2945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21215 (p : Pattern) (guard : d5502 p = 1) : d2598 p ≤ (0 : Int) + d2946 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2598, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21203 p hg
    simpa only [d2598, d2946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2598, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21214 p hg
    simpa only [d2598, d2946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21216 (p : Pattern) (guard : d5502 p = 1) : d2599 p ≤ (0 : Int) + d2947 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2599, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21171 p hg
    simpa only [d2599, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2599, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21215 p hg
    simpa only [d2599, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21217 (p : Pattern) (guard : d5502 p = 1) : d2506 p ≤ (0 : Int) + d2047 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2506, d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17202 p hg
    simpa only [d5502, d2506, d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2506, d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21134 p hg
    simpa only [d5502, d2506, d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21218 (p : Pattern) (guard : d5502 p = 1) : d2507 p ≤ (0 : Int) + d2048 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2507, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21135 p hg
    simpa only [d2507, d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2507, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21217 p hg
    simpa only [d2507, d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21219 (p : Pattern) (guard : d5502 p = 1) : d2518 p ≤ (0 : Int) + d2948 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2518, d2948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d2518, d2948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2518, d2948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21218 p hg
    simpa only [d2518, d2948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21220 (p : Pattern) (guard : d5502 p = 1) : d2600 p ≤ (0 : Int) + d1773 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2600, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21093 p hg
    simpa only [d2600, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2600, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2600, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21221 (p : Pattern) (guard : d5502 p = 1) : d2601 p ≤ (0 : Int) + d2949 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2601, d2949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21219 p hg
    simpa only [d2601, d2949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2601, d2949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21220 p hg
    simpa only [d2601, d2949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21222 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2052 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21223 (p : Pattern) (guard : d5502 p = 1) : d2506 p ≤ (0 : Int) + d2053 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2506, d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17202 p hg
    simpa only [d5502, d2506, d2053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2506, d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21222 p hg
    simpa only [d5502, d2506, d2053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21224 (p : Pattern) (guard : d5502 p = 1) : d2507 p ≤ (0 : Int) + d2054 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2507, d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21135 p hg
    simpa only [d2507, d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2507, d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21223 p hg
    simpa only [d2507, d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21225 (p : Pattern) (guard : d5502 p = 1) : d2518 p ≤ (0 : Int) + d2950 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2518, d2950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d2518, d2950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2518, d2950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21224 p hg
    simpa only [d2518, d2950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21226 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1779 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21227 (p : Pattern) (guard : d5502 p = 1) : d2506 p ≤ (0 : Int) + d1780 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2506, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17202 p hg
    simpa only [d5502, d2506, d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2506, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21226 p hg
    simpa only [d5502, d2506, d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21228 (p : Pattern) (guard : d5502 p = 1) : d2507 p ≤ (0 : Int) + d1781 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2507, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21135 p hg
    simpa only [d2507, d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2507, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21227 p hg
    simpa only [d2507, d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21229 (p : Pattern) (guard : d5502 p = 1) : d2600 p ≤ (0 : Int) + d1782 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2600, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21228 p hg
    simpa only [d2600, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2600, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2600, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21230 (p : Pattern) (guard : d5502 p = 1) : d2601 p ≤ (0 : Int) + d2951 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2601, d2951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21225 p hg
    simpa only [d2601, d2951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2601, d2951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21229 p hg
    simpa only [d2601, d2951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21231 (p : Pattern) (guard : d5502 p = 1) : d2601 p ≤ (0 : Int) + d2952 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21221 p hg
    simpa only [d2952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21230 p hg
    simpa only [d2952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21232 (p : Pattern) (guard : d5502 p = 1) : d2600 p ≤ (0 : Int) + d1789 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2600, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21138 p hg
    simpa only [d2600, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2600, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2600, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21233 (p : Pattern) (guard : d5502 p = 1) : d2601 p ≤ (0 : Int) + d2953 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2601, d2953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21139 p hg
    simpa only [d2601, d2953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2601, d2953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21232 p hg
    simpa only [d2601, d2953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21234 (p : Pattern) (guard : d5502 p = 1) : d2602 p ≤ (0 : Int) + d1798 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2602, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21160 p hg
    simpa only [d2602, d1798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2602, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2602, d1798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21235 (p : Pattern) (guard : d5502 p = 1) : d2603 p ≤ (0 : Int) + d2954 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2603, d2954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21161 p hg
    simpa only [d2603, d2954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2603, d2954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21234 p hg
    simpa only [d2603, d2954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21236 (p : Pattern) (guard : d5502 p = 1) : d2604 p ≤ (0 : Int) + d2955 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2604, d2955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21233 p hg
    simpa only [d2604, d2955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2604, d2955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21235 p hg
    simpa only [d2604, d2955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21237 (p : Pattern) (guard : d5502 p = 1) : d2605 p ≤ (0 : Int) + d2956 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2605, d2956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21231 p hg
    simpa only [d2605, d2956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2605, d2956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21236 p hg
    simpa only [d2605, d2956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21238 (p : Pattern) (guard : d5502 p = 1) : d2606 p ≤ (0 : Int) + d1804 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2606, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21124 p hg
    simpa only [d2606, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2606, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2606, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21239 (p : Pattern) (guard : d5502 p = 1) : d2607 p ≤ (0 : Int) + d2957 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2607, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21125 p hg
    simpa only [d2607, d2957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2607, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21238 p hg
    simpa only [d2607, d2957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21240 (p : Pattern) (guard : d5502 p = 1) : d2608 p ≤ (0 : Int) + d2958 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2608, d2958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21239 p hg
    simpa only [d2608, d2958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2608, d2958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2608, d2958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21241 (p : Pattern) (guard : d5502 p = 1) : d2609 p ≤ (0 : Int) + d2959 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2609, d2959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21236 p hg
    simpa only [d2609, d2959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2609, d2959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21240 p hg
    simpa only [d2609, d2959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21242 (p : Pattern) (guard : d5502 p = 1) : d2610 p ≤ (0 : Int) + d2960 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2610, d2960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21237 p hg
    simpa only [d2610, d2960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2610, d2960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21241 p hg
    simpa only [d2610, d2960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21243 (p : Pattern) (guard : d5502 p = 1) : d2611 p ≤ (0 : Int) + d2961 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2611, d2961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21204 p hg
    simpa only [d2611, d2961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2611, d2961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21144 p hg
    simpa only [d2611, d2961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21244 (p : Pattern) (guard : d5502 p = 1) : d2545 p ≤ (0 : Int) + d35 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d5502, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5808 p hg
    simpa only [d5502, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21245 (p : Pattern) (guard : d5502 p = 1) : d2612 p ≤ (0 : Int) + d2962 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2612, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21244 p hg
    simpa only [d2612, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2612, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21148 p hg
    simpa only [d2612, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21246 (p : Pattern) (guard : d5502 p = 1) : d2613 p ≤ (0 : Int) + d2963 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2613, d2963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21245 p hg
    simpa only [d2613, d2963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2613, d2963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21149 p hg
    simpa only [d2613, d2963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21247 (p : Pattern) (guard : d5502 p = 1) : d2614 p ≤ (0 : Int) + d2964 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2614, d2964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21243 p hg
    simpa only [d2614, d2964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2614, d2964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21246 p hg
    simpa only [d2614, d2964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21248 (p : Pattern) (guard : d5502 p = 1) : d2615 p ≤ (0 : Int) + d2965 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2615, d2965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21247 p hg
    simpa only [d2615, d2965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2615, d2965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21201 p hg
    simpa only [d2615, d2965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21249 (p : Pattern) (guard : d5502 p = 1) : d2616 p ≤ (0 : Int) + d2966 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2616, d2966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21248 p hg
    simpa only [d2616, d2966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2616, d2966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2616, d2966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21250 (p : Pattern) (guard : d5502 p = 1) : d2617 p ≤ (0 : Int) + d2967 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2617, d2967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21242 p hg
    simpa only [d2617, d2967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2617, d2967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21249 p hg
    simpa only [d2617, d2967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21251 (p : Pattern) (guard : d5502 p = 1) : d2618 p ≤ (0 : Int) + d2968 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2618, d2968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21230 p hg
    simpa only [d2618, d2968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2618, d2968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21243 p hg
    simpa only [d2618, d2968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21252 (p : Pattern) (guard : d5502 p = 1) : d2619 p ≤ (0 : Int) + d2969 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2619, d2969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21235 p hg
    simpa only [d2619, d2969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2619, d2969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21239 p hg
    simpa only [d2619, d2969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21253 (p : Pattern) (guard : d5502 p = 1) : d2620 p ≤ (0 : Int) + d2970 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2620, d2970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21251 p hg
    simpa only [d2620, d2970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2620, d2970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21252 p hg
    simpa only [d2620, d2970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21254 (p : Pattern) (guard : d5502 p = 1) : d2621 p ≤ (0 : Int) + d2971 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2621, d2971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21235 p hg
    simpa only [d2621, d2971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2621, d2971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21196 p hg
    simpa only [d2621, d2971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21255 (p : Pattern) (guard : d5502 p = 1) : d2622 p ≤ (0 : Int) + d2972 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2622, d2972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21254 p hg
    simpa only [d2622, d2972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2622, d2972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21201 p hg
    simpa only [d2622, d2972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21256 (p : Pattern) (guard : d5502 p = 1) : d2623 p ≤ (0 : Int) + d2973 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2623, d2973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21253 p hg
    simpa only [d2623, d2973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2623, d2973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21255 p hg
    simpa only [d2623, d2973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21257 (p : Pattern) (guard : d5502 p = 1) : d2624 p ≤ (0 : Int) + d2974 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2624, d2974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21246 p hg
    simpa only [d2624, d2974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2624, d2974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2624, d2974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21258 (p : Pattern) (guard : d5502 p = 1) : d2625 p ≤ (0 : Int) + d2975 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2625, d2975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21257 p hg
    simpa only [d2625, d2975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2625, d2975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2625, d2975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21259 (p : Pattern) (guard : d5502 p = 1) : d2626 p ≤ (0 : Int) + d2976 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2626, d2976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21258 p hg
    simpa only [d2626, d2976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2626, d2976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2626, d2976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21260 (p : Pattern) (guard : d5502 p = 1) : d2627 p ≤ (0 : Int) + d2977 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2627, d2977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21256 p hg
    simpa only [d2627, d2977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2627, d2977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21259 p hg
    simpa only [d2627, d2977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21261 (p : Pattern) (guard : d5502 p = 1) : d2628 p ≤ (0 : Int) + d2978 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2628, d2978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21250 p hg
    simpa only [d2628, d2978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2628, d2978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21260 p hg
    simpa only [d2628, d2978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21262 (p : Pattern) (guard : d5502 p = 1) : d2629 p ≤ (0 : Int) + d2979 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2629, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21216 p hg
    simpa only [d2629, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2629, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21261 p hg
    simpa only [d2629, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21263 (p : Pattern) (guard : d5502 p = 1) : d2630 p ≤ (0 : Int) + d2980 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2630, d2980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21239 p hg
    simpa only [d2630, d2980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2630, d2980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21200 p hg
    simpa only [d2630, d2980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21264 (p : Pattern) (guard : d5502 p = 1) : d2631 p ≤ (0 : Int) + d2981 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2631, d2981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21263 p hg
    simpa only [d2631, d2981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2631, d2981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21201 p hg
    simpa only [d2631, d2981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21265 (p : Pattern) (guard : d5502 p = 1) : d2632 p ≤ (0 : Int) + d2982 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2632, d2982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21201 p hg
    simpa only [d2632, d2982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2632, d2982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2632, d2982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21266 (p : Pattern) (guard : d5502 p = 1) : d2633 p ≤ (0 : Int) + d2983 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2633, d2983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21264 p hg
    simpa only [d2633, d2983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2633, d2983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21265 p hg
    simpa only [d2633, d2983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21267 (p : Pattern) (guard : d5502 p = 1) : d2634 p ≤ (0 : Int) + d2984 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2634, d2984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21265 p hg
    simpa only [d2634, d2984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2634, d2984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2634, d2984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21268 (p : Pattern) (guard : d5502 p = 1) : d2635 p ≤ (0 : Int) + d2985 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2635, d2985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21266 p hg
    simpa only [d2635, d2985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2635, d2985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21267 p hg
    simpa only [d2635, d2985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21269 (p : Pattern) (guard : d5502 p = 1) : d2636 p ≤ (0 : Int) + d2986 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2636, d2986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21267 p hg
    simpa only [d2636, d2986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2636, d2986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2636, d2986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21270 (p : Pattern) (guard : d5502 p = 1) : d2637 p ≤ (0 : Int) + d2987 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2637, d2987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21268 p hg
    simpa only [d2637, d2987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2637, d2987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21269 p hg
    simpa only [d2637, d2987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21271 (p : Pattern) (guard : d5502 p = 1) : d2638 p ≤ (0 : Int) + d2988 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2638, d2988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21261 p hg
    simpa only [d2638, d2988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2638, d2988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21270 p hg
    simpa only [d2638, d2988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21272 (p : Pattern) (guard : d5502 p = 1) : d2639 p ≤ (0 : Int) + d2989 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2639, d2989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21262 p hg
    simpa only [d2639, d2989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2639, d2989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21271 p hg
    simpa only [d2639, d2989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21273 (p : Pattern) (guard : d5502 p = 1) : d2640 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21105 p hg
    simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21108 p hg
    simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21274 (p : Pattern) (guard : d5502 p = 1) : d2641 p ≤ (0 : Int) + d2900 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2641, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21273 p hg
    simpa only [d2641, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2641, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21119 p hg
    simpa only [d2641, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21275 (p : Pattern) (guard : d5502 p = 1) : d2642 p ≤ (0 : Int) + d2905 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2642, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21274 p hg
    simpa only [d2642, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2642, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21132 p hg
    simpa only [d2642, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21276 (p : Pattern) (guard : d5502 p = 1) : d2643 p ≤ (0 : Int) + d2921 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2643, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21275 p hg
    simpa only [d2643, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2643, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21170 p hg
    simpa only [d2643, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21277 (p : Pattern) (guard : d5502 p = 1) : d2644 p ≤ (0 : Int) + d2924 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2644, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21108 p hg
    simpa only [d2644, d2924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2644, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21186 p hg
    simpa only [d2644, d2924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21278 (p : Pattern) (guard : d5502 p = 1) : d2645 p ≤ (0 : Int) + d2926 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2645, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21277 p hg
    simpa only [d2645, d2926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2645, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21188 p hg
    simpa only [d2645, d2926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21279 (p : Pattern) (guard : d5502 p = 1) : d2646 p ≤ (0 : Int) + d2934 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2646, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21278 p hg
    simpa only [d2646, d2934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2646, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21202 p hg
    simpa only [d2646, d2934, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
