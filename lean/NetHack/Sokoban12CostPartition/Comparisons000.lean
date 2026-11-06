/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions22
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare0 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (0 : Int) + d75 p := by
  omega
theorem compare1 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (18 : Int) + d75 p := by
  omega
theorem compare2 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (2 : Int) + d75 p := by
  omega
theorem compare3 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (1 : Int) + d75 p := by
  omega
theorem compare4 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (19 : Int) + d75 p := by
  omega
theorem compare5 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) ≤ (2 : Int) + 2
  decide
theorem compare6 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d4 p := by
  change (2 : Int) ≤ (2 : Int) + 4
  decide
theorem compare7 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (2 : Int) + d54 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d6, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d6, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (2 : Int) + d55 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d7, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d7, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d7, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7 p hg
    simpa only [d7, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d55 p := by
  omega
theorem compare10 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (2 : Int) + d55 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (2 : Int) + d55 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d3 p := by
  change (1 : Int) ≤ (2 : Int) + 3
  decide
theorem compare13 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (2 : Int) + d9 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d8, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12 p hg
    simpa only [d8, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d5 p := by
  change (3 : Int) ≤ (2 : Int) + 5
  decide
theorem compare15 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (2 : Int) + d58 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d9, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14 p hg
    simpa only [d9, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (2 : Int) + d59 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13 p hg
    simpa only [d10, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15 p hg
    simpa only [d10, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (2 : Int) + d60 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d11, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13 p hg
    simpa only [d11, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d11, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16 p hg
    simpa only [d11, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d12, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8 p hg
    simpa only [d12, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d12, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d12, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (2 : Int) + d60 p := by
  omega
theorem compare20 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (2 : Int) + d60 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (2 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10 p hg
    simpa only [d62, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d62, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (2 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23 (p : Pattern) (guard : d1 p = 1) : d64 p ≤ (2 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d64, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11 p hg
    simpa only [d64, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d64, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d64, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (2 : Int) + d66 p := by
  omega
theorem compare25 (p : Pattern) (guard : d1 p = 1) : d67 p ≤ (2 : Int) + d66 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (2 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (2 : Int) + d65 p := by
  omega
theorem compare28 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (2 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (2 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26 p hg
    simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (2 : Int) + d66 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31 (p : Pattern) (guard : d1 p = 1) : d72 p ≤ (2 : Int) + d66 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32 (p : Pattern) (guard : d1 p = 1) : d73 p ≤ (2 : Int) + d66 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30 p hg
    simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33 (p : Pattern) (guard : d1 p = 1) : d74 p ≤ (2 : Int) + d66 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31 p hg
    simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32 p hg
    simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (2 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35 (p : Pattern) (guard : d735 p = 1) : d75 p ≤ (2 : Int) + d66 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d735, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33 p hg
    simpa only [d735, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d735, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d735, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36 (p : Pattern) (guard : d735 p = 1) : d75 p ≤ (0 : Int) + d75 p := by
  omega
theorem compare37 (p : Pattern) (guard : d0 p = 1) : d74 p ≤ (2 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38 (p : Pattern) (guard : d737 p = 1) : d66 p ≤ (2 : Int) + d66 p := by
  omega
theorem compare39 (p : Pattern) (guard : d738 p = 1) : d75 p ≤ (2 : Int) + d66 p := by
  cases selected : p 108 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d738, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d738, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d737 p = 1 := by simpa only [d738, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38 p hg
    simpa only [d738, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40 (p : Pattern) (guard : d1 p = 1) : d161 p ≤ (0 : Int) + d161 p := by
  omega
theorem compare41 (p : Pattern) (guard : d1 p = 1) : d161 p ≤ (1 : Int) + d161 p := by
  omega
theorem compare42 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (0 : Int) + d134 p := by
  omega
theorem compare43 (p : Pattern) (guard : d0 p = 1) : d135 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44 (p : Pattern) (guard : d740 p = 1) : d136 p ≤ (0 : Int) + d199 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d740, d136, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42 p hg
    simpa only [d740, d136, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d740, d136, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43 p hg
    simpa only [d740, d136, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45 (p : Pattern) (guard : d1 p = 1) : d152 p ≤ (0 : Int) + d152 p := by
  omega
theorem compare46 (p : Pattern) (guard : d0 p = 1) : d159 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47 (p : Pattern) (guard : d740 p = 1) : d160 p ≤ (0 : Int) + d200 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d740, d160, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d740, d160, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d740, d160, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46 p hg
    simpa only [d740, d160, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48 (p : Pattern) (guard : d740 p = 1) : d161 p ≤ (0 : Int) + d201 p := by
  cases selected : p 108 with
  | false =>
    have hg : d740 p = 1 := by simpa only [d161, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44 p hg
    simpa only [d161, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d740 p = 1 := by simpa only [d161, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47 p hg
    simpa only [d161, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49 (p : Pattern) (guard : d0 p = 1) : d134 p ≤ (2 : Int) + d747 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare50 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (2 : Int) + d57 p := by
  omega
theorem compare51 (p : Pattern) (guard : d0 p = 1) : d114 p ≤ (2 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare52 (p : Pattern) (guard : d742 p = 1) : d115 p ≤ (2 : Int) + d57 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare50 p hg
    simpa only [d742, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare51 p hg
    simpa only [d742, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare53 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (2 : Int) + d63 p := by
  omega
theorem compare54 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (2 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare55 (p : Pattern) (guard : d742 p = 1) : d117 p ≤ (2 : Int) + d63 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d742, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare54 p hg
    simpa only [d742, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare56 (p : Pattern) (guard : d742 p = 1) : d118 p ≤ (2 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d118, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare52 p hg
    simpa only [d118, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d118, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare55 p hg
    simpa only [d118, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare57 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (2 : Int) + d106 p := by
  omega
theorem compare58 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (2 : Int) + d55 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare59 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (2 : Int) + d55 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare58 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare60 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (2 : Int) + d55 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare59 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare61 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (2 : Int) + d107 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d122, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d122, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare62 (p : Pattern) (guard : d0 p = 1) : d123 p ≤ (2 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare63 (p : Pattern) (guard : d742 p = 1) : d124 p ≤ (2 : Int) + d107 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare61 p hg
    simpa only [d742, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d742, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare64 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (2 : Int) + d109 p := by
  omega
theorem compare65 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (2 : Int) + d60 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare66 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (2 : Int) + d60 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare65 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare67 (p : Pattern) (guard : d1 p = 1) : d127 p ≤ (2 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare59 p hg
    simpa only [d127, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare66 p hg
    simpa only [d127, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare68 (p : Pattern) (guard : d1 p = 1) : d128 p ≤ (2 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare67 p hg
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare69 (p : Pattern) (guard : d1 p = 1) : d129 p ≤ (2 : Int) + d110 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d129, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d129, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d129, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare68 p hg
    simpa only [d129, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare70 (p : Pattern) (guard : d0 p = 1) : d130 p ≤ (2 : Int) + d110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare71 (p : Pattern) (guard : d742 p = 1) : d131 p ≤ (2 : Int) + d110 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare69 p hg
    simpa only [d742, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d742, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare72 (p : Pattern) (guard : d742 p = 1) : d132 p ≤ (2 : Int) + d336 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d132, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare63 p hg
    simpa only [d132, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d132, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare71 p hg
    simpa only [d132, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare73 (p : Pattern) (guard : d742 p = 1) : d133 p ≤ (2 : Int) + d744 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d133, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare56 p hg
    simpa only [d133, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d133, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare72 p hg
    simpa only [d133, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare74 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d0 p := by
  change (2 : Int) ≤ (2 : Int) + 0
  decide
theorem compare75 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d2 p := by
  change (4 : Int) ≤ (2 : Int) + 2
  decide
theorem compare76 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (2 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare75 p hg
    simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare77 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare76 p hg
    simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare78 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare77 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare79 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare77 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare78 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare80 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d114 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare79 p hg
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare81 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (2 : Int) + d114 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare82 (p : Pattern) (guard : d742 p = 1) : d55 p ≤ (2 : Int) + d114 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare80 p hg
    simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare81 p hg
    simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare83 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d1 p := by
  change (3 : Int) ≤ (2 : Int) + 1
  decide
theorem compare84 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (2 : Int) + d8 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare83 p hg
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare85 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (2 : Int) + d3 p := by
  change (5 : Int) ≤ (2 : Int) + 3
  decide
theorem compare86 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (2 : Int) + d9 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare75 p hg
    simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare85 p hg
    simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare87 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (2 : Int) + d10 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare84 p hg
    simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare86 p hg
    simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare88 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (2 : Int) + d11 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare84 p hg
    simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare87 p hg
    simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare89 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (2 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare77 p hg
    simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare88 p hg
    simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare90 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (2 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare88 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare91 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (2 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare78 p hg
    simpa only [d65, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare90 p hg
    simpa only [d65, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare92 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (2 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare89 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare91 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare93 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (2 : Int) + d116 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare92 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare94 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (2 : Int) + d116 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare95 (p : Pattern) (guard : d742 p = 1) : d65 p ≤ (2 : Int) + d116 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare93 p hg
    simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare94 p hg
    simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare96 (p : Pattern) (guard : d742 p = 1) : d66 p ≤ (2 : Int) + d335 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d66, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare82 p hg
    simpa only [d66, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d66, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare95 p hg
    simpa only [d66, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare97 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare77 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare98 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare77 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare97 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare99 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare98 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare100 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d123 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare99 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare101 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (2 : Int) + d123 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare102 (p : Pattern) (guard : d742 p = 1) : d55 p ≤ (2 : Int) + d123 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare101 p hg
    simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare103 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (2 : Int) + d125 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare88 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare104 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (2 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare88 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare103 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare105 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (2 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare98 p hg
    simpa only [d65, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare104 p hg
    simpa only [d65, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare106 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (2 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare105 p hg
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare107 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (2 : Int) + d130 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare106 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare108 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (2 : Int) + d130 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare109 (p : Pattern) (guard : d742 p = 1) : d65 p ≤ (2 : Int) + d130 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare107 p hg
    simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare108 p hg
    simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare110 (p : Pattern) (guard : d742 p = 1) : d66 p ≤ (2 : Int) + d745 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d66, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare102 p hg
    simpa only [d66, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d66, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare109 p hg
    simpa only [d66, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare111 (p : Pattern) (guard : d742 p = 1) : d66 p ≤ (2 : Int) + d746 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare96 p hg
    simpa only [d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare110 p hg
    simpa only [d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare112 (p : Pattern) (guard : d742 p = 1) : d135 p ≤ (2 : Int) + d747 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d135, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare73 p hg
    simpa only [d135, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d135, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare111 p hg
    simpa only [d135, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare113 (p : Pattern) (guard : d743 p = 1) : d136 p ≤ (2 : Int) + d747 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d743, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49 p hg
    simpa only [d743, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d743, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare112 p hg
    simpa only [d743, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare114 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (2 : Int) + d750 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare115 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (2 : Int) + d7 p := by
  omega
theorem compare116 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (2 : Int) + d7 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare115 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare77 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare117 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (2 : Int) + d7 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare115 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare116 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare118 (p : Pattern) (guard : d1 p = 1) : d137 p ≤ (2 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare116 p hg
    simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare119 (p : Pattern) (guard : d1 p = 1) : d139 p ≤ (2 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d139, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare117 p hg
    simpa only [d139, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d139, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare118 p hg
    simpa only [d139, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare120 (p : Pattern) (guard : d1 p = 1) : d153 p ≤ (2 : Int) + d57 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare50 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare119 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare121 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (2 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare122 (p : Pattern) (guard : d742 p = 1) : d154 p ≤ (2 : Int) + d57 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare120 p hg
    simpa only [d742, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare121 p hg
    simpa only [d742, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare123 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (2 : Int) + d11 p := by
  omega
theorem compare124 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (2 : Int) + d11 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare123 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare88 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare125 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (2 : Int) + d11 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare123 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare124 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare126 (p : Pattern) (guard : d1 p = 1) : d127 p ≤ (2 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare117 p hg
    simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare125 p hg
    simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare127 (p : Pattern) (guard : d1 p = 1) : d143 p ≤ (2 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare124 p hg
    simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare128 (p : Pattern) (guard : d1 p = 1) : d144 p ≤ (2 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare118 p hg
    simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare127 p hg
    simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare129 (p : Pattern) (guard : d1 p = 1) : d146 p ≤ (2 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d146, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare126 p hg
    simpa only [d146, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d146, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare128 p hg
    simpa only [d146, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare130 (p : Pattern) (guard : d1 p = 1) : d155 p ≤ (2 : Int) + d63 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare129 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare131 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (2 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare132 (p : Pattern) (guard : d742 p = 1) : d156 p ≤ (2 : Int) + d63 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare130 p hg
    simpa only [d742, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare131 p hg
    simpa only [d742, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare133 (p : Pattern) (guard : d742 p = 1) : d157 p ≤ (2 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d157, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare122 p hg
    simpa only [d157, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d157, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare132 p hg
    simpa only [d157, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare134 (p : Pattern) (guard : d742 p = 1) : d66 p ≤ (2 : Int) + d66 p := by
  omega
theorem compare135 (p : Pattern) (guard : d742 p = 1) : d158 p ≤ (2 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d158, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare133 p hg
    simpa only [d158, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d158, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare134 p hg
    simpa only [d158, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare136 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare97 p hg
    simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare137 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare98 p hg
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare136 p hg
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare138 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare137 p hg
    simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare139 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (2 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban12CostPartition
