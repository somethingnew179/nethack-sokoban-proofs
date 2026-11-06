/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions28
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare0 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (0 : Int) + d134 p := by
  omega
theorem compare1 (p : Pattern) (guard : d1 p = 1) : d67 p ≤ (1 : Int) + d67 p := by
  omega
theorem compare2 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (1 : Int) + d28 p := by
  omega
theorem compare3 (p : Pattern) (guard : d1 p = 1) : d27 p ≤ (1 : Int) + d27 p := by
  omega
theorem compare4 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (1 : Int) + d40 p := by
  omega
theorem compare5 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (1 : Int) + d2 p := by
  change (1 : Int) ≤ (1 : Int) + 2
  decide
theorem compare6 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d2 p := by
  omega
theorem compare7 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (1 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (1 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (1 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (1 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (1 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (1 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (1 : Int) + d68 p := by
  omega
theorem compare15 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (1 : Int) + d68 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (1 : Int) + d24 p := by
  omega
theorem compare17 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (1 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (1 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (1 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (1 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (1 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (1 : Int) + d70 p := by
  omega
theorem compare23 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (1 : Int) + d70 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24 (p : Pattern) (guard : d1 p = 1) : d72 p ≤ (1 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d72, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15 p hg
    simpa only [d72, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d72, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d72, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25 (p : Pattern) (guard : d1 p = 1) : d73 p ≤ (1 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d73, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3 p hg
    simpa only [d73, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d73, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d73, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26 (p : Pattern) (guard : d1 p = 1) : d74 p ≤ (1 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d74, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2 p hg
    simpa only [d74, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d74, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d74, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27 (p : Pattern) (guard : d1 p = 1) : d77 p ≤ (1 : Int) + d77 p := by
  omega
theorem compare28 (p : Pattern) (guard : d1 p = 1) : d78 p ≤ (1 : Int) + d77 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26 p hg
    simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29 (p : Pattern) (guard : d1 p = 1) : d83 p ≤ (1 : Int) + d83 p := by
  omega
theorem compare30 (p : Pattern) (guard : d1 p = 1) : d84 p ≤ (1 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d84, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d84, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d84, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d84, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31 (p : Pattern) (guard : d1 p = 1) : d85 p ≤ (1 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d85, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1 p hg
    simpa only [d85, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d85, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30 p hg
    simpa only [d85, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32 (p : Pattern) (guard : d1 p = 1) : d45 p ≤ (1 : Int) + d45 p := by
  omega
theorem compare33 (p : Pattern) (guard : d1 p = 1) : d89 p ≤ (1 : Int) + d89 p := by
  omega
theorem compare34 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (1 : Int) + d86 p := by
  omega
theorem compare35 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (1 : Int) + d33 p := by
  omega
theorem compare36 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (1 : Int) + d4 p := by
  omega
theorem compare37 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (1 : Int) + d0 p := by
  omega
theorem compare38 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (1 : Int) + d3 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (1 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38 p hg
    simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (1 : Int) + d18 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36 p hg
    simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39 p hg
    simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (1 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39 p hg
    simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (1 : Int) + d20 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40 p hg
    simpa only [d33, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41 p hg
    simpa only [d33, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (1 : Int) + d119 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (1 : Int) + d58 p := by
  omega
theorem compare45 (p : Pattern) (guard : d1 p = 1) : d90 p ≤ (1 : Int) + d120 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d90, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43 p hg
    simpa only [d90, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d90, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44 p hg
    simpa only [d90, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46 (p : Pattern) (guard : d1 p = 1) : d91 p ≤ (1 : Int) + d121 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d91, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d91, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d91, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d91, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47 (p : Pattern) (guard : d1 p = 1) : d93 p ≤ (1 : Int) + d93 p := by
  omega
theorem compare48 (p : Pattern) (guard : d1 p = 1) : d94 p ≤ (1 : Int) + d122 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d94, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46 p hg
    simpa only [d94, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d94, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47 p hg
    simpa only [d94, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49 (p : Pattern) (guard : d1 p = 1) : d95 p ≤ (1 : Int) + d123 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d95, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33 p hg
    simpa only [d95, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d95, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48 p hg
    simpa only [d95, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare50 (p : Pattern) (guard : d1 p = 1) : d96 p ≤ (1 : Int) + d124 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d96, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32 p hg
    simpa only [d96, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d96, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49 p hg
    simpa only [d96, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare51 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (1 : Int) + d102 p := by
  omega
theorem compare52 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (1 : Int) + d14 p := by
  omega
theorem compare53 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (1 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8 p hg
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare54 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (1 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare55 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (1 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare52 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare54 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare56 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (1 : Int) + d97 p := by
  omega
theorem compare57 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (1 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare55 p hg
    simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare56 p hg
    simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare58 (p : Pattern) (guard : d1 p = 1) : d99 p ≤ (1 : Int) + d109 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d99, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d99, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d99, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d99, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare59 (p : Pattern) (guard : d1 p = 1) : d100 p ≤ (1 : Int) + d110 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d100, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d100, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d100, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare58 p hg
    simpa only [d100, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare60 (p : Pattern) (guard : d1 p = 1) : d101 p ≤ (1 : Int) + d125 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d101, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare58 p hg
    simpa only [d101, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d101, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d101, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare61 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (1 : Int) + d126 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare59 p hg
    simpa only [d102, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d102, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare62 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (1 : Int) + d127 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare51 p hg
    simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare61 p hg
    simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare63 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (1 : Int) + d128 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare50 p hg
    simpa only [d103, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d103, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare64 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (1 : Int) + d8 p := by
  omega
theorem compare65 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (1 : Int) + d1 p := by
  change (0 : Int) ≤ (1 : Int) + 1
  decide
theorem compare66 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (1 : Int) + d9 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare65 p hg
    simpa only [d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare67 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (1 : Int) + d10 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare65 p hg
    simpa only [d4, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare66 p hg
    simpa only [d4, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare68 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (1 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare65 p hg
    simpa only [d5, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d5, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare69 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare67 p hg
    simpa only [d6, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare68 p hg
    simpa only [d6, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare70 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (1 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare67 p hg
    simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare71 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (1 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare69 p hg
    simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare72 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (1 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare71 p hg
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare73 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (1 : Int) + d52 p := by
  omega
theorem compare74 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (1 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare72 p hg
    simpa only [d86, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare73 p hg
    simpa only [d86, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare75 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (1 : Int) + d20 p := by
  omega
theorem compare76 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (1 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare66 p hg
    simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare77 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (1 : Int) + d22 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare67 p hg
    simpa only [d18, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare76 p hg
    simpa only [d18, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare78 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (1 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare76 p hg
    simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare79 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (1 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare77 p hg
    simpa only [d20, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare78 p hg
    simpa only [d20, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare80 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (1 : Int) + d25 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare75 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare79 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare81 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (1 : Int) + d54 p := by
  omega
theorem compare82 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (1 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare80 p hg
    simpa only [d87, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare81 p hg
    simpa only [d87, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare83 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (1 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d88, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d88, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d88, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare82 p hg
    simpa only [d88, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare84 (p : Pattern) (guard : d1 p = 1) : d89 p ≤ (1 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d89, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d89, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d89, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare83 p hg
    simpa only [d89, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare85 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (1 : Int) + d75 p := by
  omega
theorem compare86 (p : Pattern) (guard : d1 p = 1) : d104 p ≤ (1 : Int) + d81 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d104, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare83 p hg
    simpa only [d104, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d104, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare85 p hg
    simpa only [d104, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare87 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (1 : Int) + d82 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare84 p hg
    simpa only [d105, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare86 p hg
    simpa only [d105, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare88 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (1 : Int) + d129 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d106, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare87 p hg
    simpa only [d106, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare89 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (1 : Int) + d111 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare58 p hg
    simpa only [d107, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d107, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare90 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (1 : Int) + d112 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d108, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare59 p hg
    simpa only [d108, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d108, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare89 p hg
    simpa only [d108, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare91 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (1 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare54 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare92 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (1 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare93 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (1 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare91 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare92 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare94 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (1 : Int) + d2 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare91 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare93 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare95 (p : Pattern) (guard : d1 p = 1) : d111 p ≤ (1 : Int) + d2 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare93 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare96 (p : Pattern) (guard : d1 p = 1) : d112 p ≤ (1 : Int) + d2 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare94 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare95 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare97 (p : Pattern) (guard : d1 p = 1) : d113 p ≤ (1 : Int) + d130 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d113, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare90 p hg
    simpa only [d113, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d113, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare96 p hg
    simpa only [d113, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare98 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (1 : Int) + d131 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d114, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare88 p hg
    simpa only [d114, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d114, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare97 p hg
    simpa only [d114, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare99 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (1 : Int) + d132 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare63 p hg
    simpa only [d115, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare98 p hg
    simpa only [d115, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare100 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (1 : Int) + d133 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31 p hg
    simpa only [d116, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare99 p hg
    simpa only [d116, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare101 (p : Pattern) (guard : d0 p = 1) : d133 p ≤ (1 : Int) + d133 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare102 (p : Pattern) (guard : d827 p = 1) : d134 p ≤ (1 : Int) + d133 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d827, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d827, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d827, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare101 p hg
    simpa only [d827, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare103 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d0 p := by
  omega
theorem compare104 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (1 : Int) + d134 p := by
  omega
theorem compare105 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (0 : Int) + d116 p := by
  omega
theorem compare106 (p : Pattern) (guard : d0 p = 1) : d133 p ≤ (0 : Int) + d172 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare107 (p : Pattern) (guard : d827 p = 1) : d134 p ≤ (0 : Int) + d173 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d827, d134, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare105 p hg
    simpa only [d827, d134, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d827, d134, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare106 p hg
    simpa only [d827, d134, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare108 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (1 : Int) + d831 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare109 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (1 : Int) + d16 p := by
  omega
theorem compare110 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (1 : Int) + d25 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42 p hg
    simpa only [d34, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16 p hg
    simpa only [d34, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare111 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (1 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42 p hg
    simpa only [d35, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare110 p hg
    simpa only [d35, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare112 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (1 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare109 p hg
    simpa only [d36, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare111 p hg
    simpa only [d36, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare113 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (1 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare68 p hg
    simpa only [d37, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d37, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare114 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (1 : Int) + d40 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare69 p hg
    simpa only [d38, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare113 p hg
    simpa only [d38, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare115 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (1 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare114 p hg
    simpa only [d41, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12 p hg
    simpa only [d41, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare116 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (1 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d42, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare114 p hg
    simpa only [d42, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d42, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare115 p hg
    simpa only [d42, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare117 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (1 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare79 p hg
    simpa only [d25, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d25, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare118 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (1 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare79 p hg
    simpa only [d26, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare117 p hg
    simpa only [d26, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare119 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (1 : Int) + d72 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare116 p hg
    simpa only [d43, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare118 p hg
    simpa only [d43, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare120 (p : Pattern) (guard : d1 p = 1) : d44 p ≤ (1 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d44, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare112 p hg
    simpa only [d44, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d44, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare119 p hg
    simpa only [d44, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare121 (p : Pattern) (guard : d1 p = 1) : d45 p ≤ (1 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d45, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2 p hg
    simpa only [d45, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d45, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare120 p hg
    simpa only [d45, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare122 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (1 : Int) + d2 p := by
  change (0 : Int) ≤ (1 : Int) + 2
  decide
theorem compare123 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (1 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare122 p hg
    simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare124 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (1 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare122 p hg
    simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare123 p hg
    simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare125 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (1 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare122 p hg
    simpa only [d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare126 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (1 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare124 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare125 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare127 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (1 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare125 p hg
    simpa only [d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare128 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (1 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare126 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare127 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare129 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (1 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare114 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare128 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare130 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (1 : Int) + d68 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare129 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare115 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare131 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (1 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare123 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare132 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (1 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare124 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare131 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare133 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (1 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare131 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare134 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (1 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare132 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare133 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare135 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (1 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare79 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare134 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare136 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (1 : Int) + d70 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare135 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare117 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare137 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (1 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare130 p hg
    simpa only [d43, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare136 p hg
    simpa only [d43, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare138 (p : Pattern) (guard : d1 p = 1) : d44 p ≤ (1 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d44, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare112 p hg
    simpa only [d44, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d44, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare137 p hg
    simpa only [d44, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare139 (p : Pattern) (guard : d1 p = 1) : d45 p ≤ (1 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d45, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2 p hg
    simpa only [d45, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d45, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare138 p hg
    simpa only [d45, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
