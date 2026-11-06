/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons187
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare26320 (p : Pattern) (guard : d5843 p = 1) : d3214 p ≤ (0 : Int) + d4026 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3214, d4026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26128 p hg
    simpa only [d3214, d4026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3214, d4026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25918 p hg
    simpa only [d3214, d4026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26321 (p : Pattern) (guard : d5843 p = 1) : d3215 p ≤ (0 : Int) + d4027 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3215, d4027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26320 p hg
    simpa only [d3215, d4027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3215, d4027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3215, d4027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26322 (p : Pattern) (guard : d5843 p = 1) : d3216 p ≤ (0 : Int) + d4028 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3216, d4028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26321 p hg
    simpa only [d3216, d4028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3216, d4028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3216, d4028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26323 (p : Pattern) (guard : d5843 p = 1) : d3217 p ≤ (0 : Int) + d4029 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3217, d4029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26319 p hg
    simpa only [d3217, d4029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3217, d4029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26322 p hg
    simpa only [d3217, d4029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26324 (p : Pattern) (guard : d5843 p = 1) : d3218 p ≤ (0 : Int) + d4030 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3218, d4030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26323 p hg
    simpa only [d3218, d4030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3218, d4030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26312 p hg
    simpa only [d3218, d4030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26325 (p : Pattern) (guard : d5843 p = 1) : d3219 p ≤ (0 : Int) + d4031 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3219, d4031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26324 p hg
    simpa only [d3219, d4031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3219, d4031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3219, d4031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26326 (p : Pattern) (guard : d5843 p = 1) : d3220 p ≤ (0 : Int) + d4032 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3220, d4032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26314 p hg
    simpa only [d3220, d4032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3220, d4032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26325 p hg
    simpa only [d3220, d4032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26327 (p : Pattern) (guard : d5843 p = 1) : d3221 p ≤ (0 : Int) + d4033 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3221, d4033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26254 p hg
    simpa only [d3221, d4033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3221, d4033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26326 p hg
    simpa only [d3221, d4033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26328 (p : Pattern) (guard : d5843 p = 1) : d3222 p ≤ (0 : Int) + d4034 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3222, d4034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26003 p hg
    simpa only [d3222, d4034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3222, d4034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26327 p hg
    simpa only [d3222, d4034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26329 (p : Pattern) (guard : d5843 p = 1) : d3223 p ≤ (0 : Int) + d4035 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3223, d4035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26235 p hg
    simpa only [d3223, d4035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3223, d4035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26328 p hg
    simpa only [d3223, d4035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26330 (p : Pattern) (guard : d5843 p = 1) : d3224 p ≤ (0 : Int) + d4036 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3224, d4036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26160 p hg
    simpa only [d3224, d4036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3224, d4036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26329 p hg
    simpa only [d3224, d4036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26331 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26332 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26333 (p : Pattern) (guard : d5843 p = 1) : d13 p ≤ (0 : Int) + d0 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26332 p hg
    simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26334 (p : Pattern) (guard : d6326 p = 1) : d14 p ≤ (0 : Int) + d0 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26331 p hg
    simpa only [d6326, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26333 p hg
    simpa only [d6326, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26335 (p : Pattern) (guard : d6326 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare26336 (p : Pattern) (guard : d6326 p = 1) : d15 p ≤ (0 : Int) + d6327 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d15, d6327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26334 p hg
    simpa only [d15, d6327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d15, d6327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d15, d6327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26337 (p : Pattern) (guard : d6326 p = 1) : d16 p ≤ (0 : Int) + d6328 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d16, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26334 p hg
    simpa only [d16, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d16, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26336 p hg
    simpa only [d16, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26338 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (0 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26339 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26340 (p : Pattern) (guard : d5843 p = 1) : d17 p ≤ (0 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26339 p hg
    simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26341 (p : Pattern) (guard : d6326 p = 1) : d18 p ≤ (0 : Int) + d4 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26338 p hg
    simpa only [d6326, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26340 p hg
    simpa only [d6326, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26342 (p : Pattern) (guard : d6326 p = 1) : d19 p ≤ (0 : Int) + d6329 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d19, d6329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26341 p hg
    simpa only [d19, d6329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d19, d6329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d19, d6329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26343 (p : Pattern) (guard : d6326 p = 1) : d20 p ≤ (0 : Int) + d6330 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d20, d6330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26341 p hg
    simpa only [d20, d6330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d20, d6330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26342 p hg
    simpa only [d20, d6330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26344 (p : Pattern) (guard : d6326 p = 1) : d21 p ≤ (0 : Int) + d6331 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d21, d6331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26337 p hg
    simpa only [d21, d6331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d21, d6331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26343 p hg
    simpa only [d21, d6331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26345 (p : Pattern) (guard : d6326 p = 1) : d22 p ≤ (0 : Int) + d6332 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d22, d6332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26337 p hg
    simpa only [d22, d6332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d22, d6332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26344 p hg
    simpa only [d22, d6332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26346 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (0 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26347 (p : Pattern) (guard : d6326 p = 1) : d24 p ≤ (0 : Int) + d9 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26346 p hg
    simpa only [d6326, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23418 p hg
    simpa only [d6326, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26348 (p : Pattern) (guard : d6326 p = 1) : d25 p ≤ (0 : Int) + d6333 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d25, d6333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26347 p hg
    simpa only [d25, d6333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d25, d6333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d25, d6333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26349 (p : Pattern) (guard : d6326 p = 1) : d26 p ≤ (0 : Int) + d6334 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d26, d6334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26347 p hg
    simpa only [d26, d6334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d26, d6334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26348 p hg
    simpa only [d26, d6334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26350 (p : Pattern) (guard : d6326 p = 1) : d27 p ≤ (0 : Int) + d6335 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d27, d6335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26349 p hg
    simpa only [d27, d6335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d27, d6335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d27, d6335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26351 (p : Pattern) (guard : d6326 p = 1) : d28 p ≤ (0 : Int) + d6336 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d28, d6336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26344 p hg
    simpa only [d28, d6336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d28, d6336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26350 p hg
    simpa only [d28, d6336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26352 (p : Pattern) (guard : d6326 p = 1) : d29 p ≤ (0 : Int) + d6337 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d29, d6337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26345 p hg
    simpa only [d29, d6337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d29, d6337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26351 p hg
    simpa only [d29, d6337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26353 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26354 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26355 (p : Pattern) (guard : d5843 p = 1) : d30 p ≤ (0 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26354 p hg
    simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26356 (p : Pattern) (guard : d6326 p = 1) : d31 p ≤ (0 : Int) + d2 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26353 p hg
    simpa only [d6326, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26355 p hg
    simpa only [d6326, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26357 (p : Pattern) (guard : d6326 p = 1) : d32 p ≤ (0 : Int) + d6338 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d32, d6338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26356 p hg
    simpa only [d32, d6338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d32, d6338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d32, d6338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26358 (p : Pattern) (guard : d6326 p = 1) : d33 p ≤ (0 : Int) + d6339 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d33, d6339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26334 p hg
    simpa only [d33, d6339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d33, d6339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26357 p hg
    simpa only [d33, d6339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26359 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (0 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26360 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26361 (p : Pattern) (guard : d5843 p = 1) : d34 p ≤ (0 : Int) + d6 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14566 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26360 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26362 (p : Pattern) (guard : d6326 p = 1) : d35 p ≤ (0 : Int) + d6 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26359 p hg
    simpa only [d6326, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26361 p hg
    simpa only [d6326, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26363 (p : Pattern) (guard : d6326 p = 1) : d36 p ≤ (0 : Int) + d6340 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d36, d6340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26362 p hg
    simpa only [d36, d6340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d36, d6340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d36, d6340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26364 (p : Pattern) (guard : d6326 p = 1) : d37 p ≤ (0 : Int) + d6341 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d37, d6341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26334 p hg
    simpa only [d37, d6341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d37, d6341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26363 p hg
    simpa only [d37, d6341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26365 (p : Pattern) (guard : d6326 p = 1) : d38 p ≤ (0 : Int) + d6342 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d38, d6342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26358 p hg
    simpa only [d38, d6342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d38, d6342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26364 p hg
    simpa only [d38, d6342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26366 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (0 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26367 (p : Pattern) (guard : d6326 p = 1) : d40 p ≤ (0 : Int) + d11 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26366 p hg
    simpa only [d6326, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23452 p hg
    simpa only [d6326, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26368 (p : Pattern) (guard : d6326 p = 1) : d41 p ≤ (0 : Int) + d6343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d41, d6343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26367 p hg
    simpa only [d41, d6343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d41, d6343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d41, d6343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26369 (p : Pattern) (guard : d6326 p = 1) : d42 p ≤ (0 : Int) + d6344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d42, d6344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26334 p hg
    simpa only [d42, d6344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d42, d6344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26368 p hg
    simpa only [d42, d6344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26370 (p : Pattern) (guard : d6326 p = 1) : d43 p ≤ (0 : Int) + d6345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d43, d6345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26341 p hg
    simpa only [d43, d6345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d43, d6345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d43, d6345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26371 (p : Pattern) (guard : d6326 p = 1) : d44 p ≤ (0 : Int) + d6346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d44, d6346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26369 p hg
    simpa only [d44, d6346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d44, d6346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26370 p hg
    simpa only [d44, d6346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26372 (p : Pattern) (guard : d6326 p = 1) : d45 p ≤ (0 : Int) + d6347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d45, d6347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26365 p hg
    simpa only [d45, d6347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d45, d6347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26371 p hg
    simpa only [d45, d6347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26373 (p : Pattern) (guard : d6326 p = 1) : d46 p ≤ (0 : Int) + d6348 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d46, d6348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26334 p hg
    simpa only [d46, d6348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d46, d6348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d46, d6348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26374 (p : Pattern) (guard : d6326 p = 1) : d47 p ≤ (0 : Int) + d6349 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d47, d6349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26373 p hg
    simpa only [d47, d6349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d47, d6349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26370 p hg
    simpa only [d47, d6349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26375 (p : Pattern) (guard : d6326 p = 1) : d48 p ≤ (0 : Int) + d6350 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d48, d6350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26347 p hg
    simpa only [d48, d6350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d48, d6350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d48, d6350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26376 (p : Pattern) (guard : d6326 p = 1) : d49 p ≤ (0 : Int) + d6351 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d49, d6351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26375 p hg
    simpa only [d49, d6351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d49, d6351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d49, d6351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26377 (p : Pattern) (guard : d6326 p = 1) : d50 p ≤ (0 : Int) + d6352 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d50, d6352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26374 p hg
    simpa only [d50, d6352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d50, d6352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26376 p hg
    simpa only [d50, d6352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26378 (p : Pattern) (guard : d6326 p = 1) : d51 p ≤ (0 : Int) + d6353 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d51, d6353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26372 p hg
    simpa only [d51, d6353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d51, d6353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26377 p hg
    simpa only [d51, d6353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26379 (p : Pattern) (guard : d6326 p = 1) : d52 p ≤ (0 : Int) + d6354 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d52, d6354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26352 p hg
    simpa only [d52, d6354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d52, d6354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26378 p hg
    simpa only [d52, d6354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26380 (p : Pattern) (guard : d6326 p = 1) : d53 p ≤ (0 : Int) + d6355 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d53, d6355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26356 p hg
    simpa only [d53, d6355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d53, d6355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26357 p hg
    simpa only [d53, d6355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26381 (p : Pattern) (guard : d6326 p = 1) : d54 p ≤ (0 : Int) + d6356 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d54, d6356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26337 p hg
    simpa only [d54, d6356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d54, d6356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26380 p hg
    simpa only [d54, d6356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26382 (p : Pattern) (guard : d6326 p = 1) : d55 p ≤ (0 : Int) + d6357 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d55, d6357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26343 p hg
    simpa only [d55, d6357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d55, d6357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26349 p hg
    simpa only [d55, d6357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26383 (p : Pattern) (guard : d6326 p = 1) : d56 p ≤ (0 : Int) + d6358 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d56, d6358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26381 p hg
    simpa only [d56, d6358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d56, d6358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26382 p hg
    simpa only [d56, d6358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26384 (p : Pattern) (guard : d0 p = 1) : d10 p ≤ (0 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26385 (p : Pattern) (guard : d6326 p = 1) : d58 p ≤ (0 : Int) + d10 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26384 p hg
    simpa only [d6326, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23494 p hg
    simpa only [d6326, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26386 (p : Pattern) (guard : d6326 p = 1) : d59 p ≤ (0 : Int) + d6359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d59, d6359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26385 p hg
    simpa only [d59, d6359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d59, d6359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d59, d6359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26387 (p : Pattern) (guard : d6326 p = 1) : d60 p ≤ (0 : Int) + d6360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d60, d6360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26385 p hg
    simpa only [d60, d6360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d60, d6360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26386 p hg
    simpa only [d60, d6360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26388 (p : Pattern) (guard : d6326 p = 1) : d61 p ≤ (0 : Int) + d6361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d61, d6361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26343 p hg
    simpa only [d61, d6361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d61, d6361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26387 p hg
    simpa only [d61, d6361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26389 (p : Pattern) (guard : d6326 p = 1) : d62 p ≤ (0 : Int) + d6362 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d62, d6362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26367 p hg
    simpa only [d62, d6362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d62, d6362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26368 p hg
    simpa only [d62, d6362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26390 (p : Pattern) (guard : d6326 p = 1) : d63 p ≤ (0 : Int) + d6363 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d63, d6363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26389 p hg
    simpa only [d63, d6363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d63, d6363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d63, d6363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26391 (p : Pattern) (guard : d6326 p = 1) : d64 p ≤ (0 : Int) + d6364 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d64, d6364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26388 p hg
    simpa only [d64, d6364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d64, d6364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26390 p hg
    simpa only [d64, d6364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26392 (p : Pattern) (guard : d6326 p = 1) : d65 p ≤ (0 : Int) + d6365 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d65, d6365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26383 p hg
    simpa only [d65, d6365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d65, d6365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26391 p hg
    simpa only [d65, d6365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26393 (p : Pattern) (guard : d6326 p = 1) : d66 p ≤ (0 : Int) + d6366 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d66, d6366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26356 p hg
    simpa only [d66, d6366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d66, d6366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d66, d6366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26394 (p : Pattern) (guard : d6326 p = 1) : d67 p ≤ (0 : Int) + d6367 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d67, d6367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26364 p hg
    simpa only [d67, d6367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d67, d6367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26393 p hg
    simpa only [d67, d6367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26395 (p : Pattern) (guard : d6326 p = 1) : d68 p ≤ (0 : Int) + d6368 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d68, d6368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26370 p hg
    simpa only [d68, d6368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d68, d6368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26375 p hg
    simpa only [d68, d6368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26396 (p : Pattern) (guard : d6326 p = 1) : d69 p ≤ (0 : Int) + d6369 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d69, d6369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26394 p hg
    simpa only [d69, d6369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d69, d6369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26395 p hg
    simpa only [d69, d6369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26397 (p : Pattern) (guard : d6326 p = 1) : d70 p ≤ (0 : Int) + d6370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d70, d6370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26385 p hg
    simpa only [d70, d6370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d70, d6370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d70, d6370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26398 (p : Pattern) (guard : d6326 p = 1) : d71 p ≤ (0 : Int) + d6371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d71, d6371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26370 p hg
    simpa only [d71, d6371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d71, d6371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26397 p hg
    simpa only [d71, d6371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26399 (p : Pattern) (guard : d6326 p = 1) : d72 p ≤ (0 : Int) + d6372 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d72, d6372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26367 p hg
    simpa only [d72, d6372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d72, d6372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d72, d6372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26400 (p : Pattern) (guard : d6326 p = 1) : d73 p ≤ (0 : Int) + d6373 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d73, d6373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26399 p hg
    simpa only [d73, d6373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d73, d6373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d73, d6373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26401 (p : Pattern) (guard : d6326 p = 1) : d74 p ≤ (0 : Int) + d6374 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d74, d6374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26398 p hg
    simpa only [d74, d6374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d74, d6374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26400 p hg
    simpa only [d74, d6374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26402 (p : Pattern) (guard : d6326 p = 1) : d75 p ≤ (0 : Int) + d6375 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d75, d6375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26396 p hg
    simpa only [d75, d6375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d75, d6375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26401 p hg
    simpa only [d75, d6375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26403 (p : Pattern) (guard : d6326 p = 1) : d76 p ≤ (0 : Int) + d6376 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d76, d6376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26392 p hg
    simpa only [d76, d6376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d76, d6376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26402 p hg
    simpa only [d76, d6376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26404 (p : Pattern) (guard : d6326 p = 1) : d77 p ≤ (0 : Int) + d6377 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d77, d6377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26379 p hg
    simpa only [d77, d6377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d77, d6377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26403 p hg
    simpa only [d77, d6377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26405 (p : Pattern) (guard : d6326 p = 1) : d78 p ≤ (0 : Int) + d6378 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d78, d6378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26362 p hg
    simpa only [d78, d6378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d78, d6378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26363 p hg
    simpa only [d78, d6378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26406 (p : Pattern) (guard : d6326 p = 1) : d79 p ≤ (0 : Int) + d6379 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d79, d6379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26380 p hg
    simpa only [d79, d6379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d79, d6379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26405 p hg
    simpa only [d79, d6379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26407 (p : Pattern) (guard : d6326 p = 1) : d80 p ≤ (0 : Int) + d6380 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d80, d6380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26406 p hg
    simpa only [d80, d6380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d80, d6380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26390 p hg
    simpa only [d80, d6380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26408 (p : Pattern) (guard : d6326 p = 1) : d81 p ≤ (0 : Int) + d6381 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d81, d6381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26407 p hg
    simpa only [d81, d6381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d81, d6381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d81, d6381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26409 (p : Pattern) (guard : d6326 p = 1) : d82 p ≤ (0 : Int) + d6382 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d82, d6382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26352 p hg
    simpa only [d82, d6382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d82, d6382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26408 p hg
    simpa only [d82, d6382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26410 (p : Pattern) (guard : d6326 p = 1) : d83 p ≤ (0 : Int) + d6383 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d83, d6383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26405 p hg
    simpa only [d83, d6383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d83, d6383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d83, d6383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26411 (p : Pattern) (guard : d6326 p = 1) : d84 p ≤ (0 : Int) + d6384 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d84, d6384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26410 p hg
    simpa only [d84, d6384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d84, d6384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d84, d6384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26412 (p : Pattern) (guard : d6326 p = 1) : d85 p ≤ (0 : Int) + d6385 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d85, d6385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26411 p hg
    simpa only [d85, d6385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d85, d6385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d85, d6385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26413 (p : Pattern) (guard : d6326 p = 1) : d86 p ≤ (0 : Int) + d6386 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d86, d6386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26392 p hg
    simpa only [d86, d6386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d86, d6386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26412 p hg
    simpa only [d86, d6386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26414 (p : Pattern) (guard : d6326 p = 1) : d87 p ≤ (0 : Int) + d6387 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d87, d6387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26409 p hg
    simpa only [d87, d6387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d87, d6387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26413 p hg
    simpa only [d87, d6387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26415 (p : Pattern) (guard : d6326 p = 1) : d88 p ≤ (0 : Int) + d6388 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d88, d6388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26404 p hg
    simpa only [d88, d6388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d88, d6388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26414 p hg
    simpa only [d88, d6388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26416 (p : Pattern) (guard : d6326 p = 1) : d89 p ≤ (0 : Int) + d6389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d89, d6389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26349 p hg
    simpa only [d89, d6389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d89, d6389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26389 p hg
    simpa only [d89, d6389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26417 (p : Pattern) (guard : d6326 p = 1) : d90 p ≤ (0 : Int) + d6390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d90, d6390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26416 p hg
    simpa only [d90, d6390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d90, d6390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26390 p hg
    simpa only [d90, d6390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26418 (p : Pattern) (guard : d6326 p = 1) : d91 p ≤ (0 : Int) + d6391 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d91, d6391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26390 p hg
    simpa only [d91, d6391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d91, d6391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d91, d6391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26419 (p : Pattern) (guard : d6326 p = 1) : d92 p ≤ (0 : Int) + d6392 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d92, d6392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26417 p hg
    simpa only [d92, d6392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d92, d6392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26418 p hg
    simpa only [d92, d6392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26420 (p : Pattern) (guard : d6326 p = 1) : d93 p ≤ (0 : Int) + d6393 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d93, d6393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26418 p hg
    simpa only [d93, d6393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d93, d6393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d93, d6393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26421 (p : Pattern) (guard : d6326 p = 1) : d94 p ≤ (0 : Int) + d6394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d94, d6394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26419 p hg
    simpa only [d94, d6394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d94, d6394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26420 p hg
    simpa only [d94, d6394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26422 (p : Pattern) (guard : d6326 p = 1) : d95 p ≤ (0 : Int) + d6395 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d95, d6395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26420 p hg
    simpa only [d95, d6395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d95, d6395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d95, d6395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26423 (p : Pattern) (guard : d6326 p = 1) : d96 p ≤ (0 : Int) + d6396 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d96, d6396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26421 p hg
    simpa only [d96, d6396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d96, d6396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26422 p hg
    simpa only [d96, d6396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26424 (p : Pattern) (guard : d6326 p = 1) : d97 p ≤ (0 : Int) + d6397 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d97, d6397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26414 p hg
    simpa only [d97, d6397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d97, d6397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26423 p hg
    simpa only [d97, d6397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26425 (p : Pattern) (guard : d6326 p = 1) : d98 p ≤ (0 : Int) + d6398 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d98, d6398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26415 p hg
    simpa only [d98, d6398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d98, d6398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26424 p hg
    simpa only [d98, d6398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26426 (p : Pattern) (guard : d6326 p = 1) : d99 p ≤ (0 : Int) + d6399 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d99, d6399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26414 p hg
    simpa only [d99, d6399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d99, d6399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d99, d6399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26427 (p : Pattern) (guard : d6326 p = 1) : d100 p ≤ (0 : Int) + d6400 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d100, d6400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26415 p hg
    simpa only [d100, d6400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d100, d6400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26426 p hg
    simpa only [d100, d6400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26428 (p : Pattern) (guard : d6326 p = 1) : d101 p ≤ (0 : Int) + d6401 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d101, d6401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26425 p hg
    simpa only [d101, d6401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d101, d6401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26427 p hg
    simpa only [d101, d6401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26429 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (0 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26430 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26431 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (0 : Int) + d1 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26430 p hg
    simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26432 (p : Pattern) (guard : d6326 p = 1) : d103 p ≤ (0 : Int) + d1 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26429 p hg
    simpa only [d6326, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26431 p hg
    simpa only [d6326, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26433 (p : Pattern) (guard : d6326 p = 1) : d104 p ≤ (0 : Int) + d6402 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d104, d6402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26432 p hg
    simpa only [d104, d6402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d104, d6402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d104, d6402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26434 (p : Pattern) (guard : d6326 p = 1) : d105 p ≤ (0 : Int) + d6403 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d105, d6403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26432 p hg
    simpa only [d105, d6403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d105, d6403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26433 p hg
    simpa only [d105, d6403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26435 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26436 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26437 (p : Pattern) (guard : d5843 p = 1) : d106 p ≤ (0 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14654 p hg
    simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26436 p hg
    simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26438 (p : Pattern) (guard : d6326 p = 1) : d107 p ≤ (0 : Int) + d5 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26435 p hg
    simpa only [d6326, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26437 p hg
    simpa only [d6326, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26439 (p : Pattern) (guard : d6326 p = 1) : d108 p ≤ (0 : Int) + d6404 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d108, d6404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26438 p hg
    simpa only [d108, d6404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d108, d6404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d108, d6404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26440 (p : Pattern) (guard : d6326 p = 1) : d109 p ≤ (0 : Int) + d6405 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d109, d6405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26438 p hg
    simpa only [d109, d6405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d109, d6405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26439 p hg
    simpa only [d109, d6405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26441 (p : Pattern) (guard : d6326 p = 1) : d110 p ≤ (0 : Int) + d6406 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d110, d6406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26434 p hg
    simpa only [d110, d6406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d110, d6406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26440 p hg
    simpa only [d110, d6406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26442 (p : Pattern) (guard : d6326 p = 1) : d111 p ≤ (0 : Int) + d6407 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d111, d6407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26434 p hg
    simpa only [d111, d6407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d111, d6407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26441 p hg
    simpa only [d111, d6407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26443 (p : Pattern) (guard : d6326 p = 1) : d112 p ≤ (0 : Int) + d6408 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d112, d6408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26387 p hg
    simpa only [d112, d6408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d112, d6408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d112, d6408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26444 (p : Pattern) (guard : d6326 p = 1) : d113 p ≤ (0 : Int) + d6409 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d113, d6409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26441 p hg
    simpa only [d113, d6409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d113, d6409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26443 p hg
    simpa only [d113, d6409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26445 (p : Pattern) (guard : d6326 p = 1) : d114 p ≤ (0 : Int) + d6410 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d114, d6410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26442 p hg
    simpa only [d114, d6410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d114, d6410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26444 p hg
    simpa only [d114, d6410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26446 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26447 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26448 (p : Pattern) (guard : d5843 p = 1) : d115 p ≤ (0 : Int) + d3 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26447 p hg
    simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26449 (p : Pattern) (guard : d6326 p = 1) : d116 p ≤ (0 : Int) + d3 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26446 p hg
    simpa only [d6326, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26448 p hg
    simpa only [d6326, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26450 (p : Pattern) (guard : d6326 p = 1) : d117 p ≤ (0 : Int) + d6411 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d117, d6411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26449 p hg
    simpa only [d117, d6411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d117, d6411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d117, d6411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26451 (p : Pattern) (guard : d6326 p = 1) : d118 p ≤ (0 : Int) + d6412 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d118, d6412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26432 p hg
    simpa only [d118, d6412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d118, d6412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26450 p hg
    simpa only [d118, d6412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26452 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26453 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26454 (p : Pattern) (guard : d5843 p = 1) : d119 p ≤ (0 : Int) + d7 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14675 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26453 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26455 (p : Pattern) (guard : d6326 p = 1) : d120 p ≤ (0 : Int) + d7 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26452 p hg
    simpa only [d6326, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26454 p hg
    simpa only [d6326, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26456 (p : Pattern) (guard : d6326 p = 1) : d121 p ≤ (0 : Int) + d6413 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d121, d6413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26455 p hg
    simpa only [d121, d6413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d121, d6413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d121, d6413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26457 (p : Pattern) (guard : d6326 p = 1) : d122 p ≤ (0 : Int) + d6414 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d122, d6414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26432 p hg
    simpa only [d122, d6414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d122, d6414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26456 p hg
    simpa only [d122, d6414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26458 (p : Pattern) (guard : d6326 p = 1) : d123 p ≤ (0 : Int) + d6415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d123, d6415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26451 p hg
    simpa only [d123, d6415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d123, d6415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26457 p hg
    simpa only [d123, d6415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26459 (p : Pattern) (guard : d6326 p = 1) : d124 p ≤ (0 : Int) + d6416 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d124, d6416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26432 p hg
    simpa only [d124, d6416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d124, d6416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d124, d6416, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
