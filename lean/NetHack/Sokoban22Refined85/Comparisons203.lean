/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons202
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare28420 (p : Pattern) (guard : d6558 p = 1) : d3530 p ≤ (0 : Int) + d7004 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3530, d7004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28419 p hg
    simpa only [d3530, d7004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3530, d7004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3530, d7004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28421 (p : Pattern) (guard : d6558 p = 1) : d3531 p ≤ (0 : Int) + d7005 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3531, d7005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28420 p hg
    simpa only [d3531, d7005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3531, d7005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3531, d7005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28422 (p : Pattern) (guard : d6558 p = 1) : d3532 p ≤ (0 : Int) + d7006 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3532, d7006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28418 p hg
    simpa only [d3532, d7006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3532, d7006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28421 p hg
    simpa only [d3532, d7006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28423 (p : Pattern) (guard : d6558 p = 1) : d3533 p ≤ (0 : Int) + d7007 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3533, d7007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28422 p hg
    simpa only [d3533, d7007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3533, d7007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28411 p hg
    simpa only [d3533, d7007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28424 (p : Pattern) (guard : d6558 p = 1) : d3534 p ≤ (0 : Int) + d7008 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3534, d7008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28423 p hg
    simpa only [d3534, d7008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3534, d7008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3534, d7008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28425 (p : Pattern) (guard : d6558 p = 1) : d3535 p ≤ (0 : Int) + d7009 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3535, d7009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28413 p hg
    simpa only [d3535, d7009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3535, d7009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28424 p hg
    simpa only [d3535, d7009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28426 (p : Pattern) (guard : d6558 p = 1) : d3536 p ≤ (0 : Int) + d7010 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3536, d7010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28354 p hg
    simpa only [d3536, d7010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3536, d7010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28425 p hg
    simpa only [d3536, d7010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28427 (p : Pattern) (guard : d6558 p = 1) : d3537 p ≤ (0 : Int) + d7011 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3537, d7011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28073 p hg
    simpa only [d3537, d7011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3537, d7011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28426 p hg
    simpa only [d3537, d7011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28428 (p : Pattern) (guard : d6558 p = 1) : d3538 p ≤ (0 : Int) + d7012 p := by
  cases selected : p 49 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3538, d7012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28335 p hg
    simpa only [d3538, d7012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3538, d7012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28427 p hg
    simpa only [d3538, d7012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28429 (p : Pattern) (guard : d6558 p = 1) : d3539 p ≤ (0 : Int) + d7013 p := by
  cases selected : p 48 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3539, d7013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28260 p hg
    simpa only [d3539, d7013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3539, d7013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28428 p hg
    simpa only [d3539, d7013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28430 (p : Pattern) (guard : d5268 p = 1) : d3228 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26606 p hg
    simpa only [d3228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28431 (p : Pattern) (guard : d5268 p = 1) : d3229 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28430 p hg
    simpa only [d3229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28432 (p : Pattern) (guard : d5268 p = 1) : d3230 p ≤ (0 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3230, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3230, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3230, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3230, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28433 (p : Pattern) (guard : d5268 p = 1) : d3231 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3231, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28431 p hg
    simpa only [d3231, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3231, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28432 p hg
    simpa only [d3231, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28434 (p : Pattern) (guard : d5268 p = 1) : d3234 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26616 p hg
    simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28435 (p : Pattern) (guard : d5268 p = 1) : d3235 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28434 p hg
    simpa only [d3235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28436 (p : Pattern) (guard : d5268 p = 1) : d3236 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3236, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28435 p hg
    simpa only [d3236, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3236, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28432 p hg
    simpa only [d3236, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28437 (p : Pattern) (guard : d5268 p = 1) : d3237 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28433 p hg
    simpa only [d3237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28436 p hg
    simpa only [d3237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28438 (p : Pattern) (guard : d5268 p = 1) : d3238 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3238, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3238, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3238, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28432 p hg
    simpa only [d3238, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28439 (p : Pattern) (guard : d5268 p = 1) : d3240 p ≤ (0 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3240, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26626 p hg
    simpa only [d3240, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3240, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3240, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28440 (p : Pattern) (guard : d5268 p = 1) : d3241 p ≤ (0 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3241, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26626 p hg
    simpa only [d3241, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3241, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28439 p hg
    simpa only [d3241, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28441 (p : Pattern) (guard : d5268 p = 1) : d3242 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3242, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28438 p hg
    simpa only [d3242, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3242, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28440 p hg
    simpa only [d3242, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28442 (p : Pattern) (guard : d5268 p = 1) : d3243 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3243, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28437 p hg
    simpa only [d3243, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3243, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28441 p hg
    simpa only [d3243, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28443 (p : Pattern) (guard : d5268 p = 1) : d3245 p ≤ (0 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3245, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26635 p hg
    simpa only [d3245, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3245, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3245, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28444 (p : Pattern) (guard : d5268 p = 1) : d3246 p ≤ (0 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3246, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26635 p hg
    simpa only [d3246, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3246, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28443 p hg
    simpa only [d3246, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28445 (p : Pattern) (guard : d5268 p = 1) : d3247 p ≤ (0 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3247, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28444 p hg
    simpa only [d3247, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3247, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3247, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28446 (p : Pattern) (guard : d5268 p = 1) : d3248 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3248, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28441 p hg
    simpa only [d3248, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3248, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28445 p hg
    simpa only [d3248, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28447 (p : Pattern) (guard : d5268 p = 1) : d3249 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3249, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28442 p hg
    simpa only [d3249, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3249, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28446 p hg
    simpa only [d3249, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28448 (p : Pattern) (guard : d5268 p = 1) : d3251 p ≤ (0 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3251, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26643 p hg
    simpa only [d3251, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3251, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3251, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28449 (p : Pattern) (guard : d5268 p = 1) : d3252 p ≤ (0 : Int) + d33 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3252, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3252, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3252, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28448 p hg
    simpa only [d3252, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28450 (p : Pattern) (guard : d5268 p = 1) : d3254 p ≤ (0 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3254, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26648 p hg
    simpa only [d3254, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3254, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3254, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28451 (p : Pattern) (guard : d5268 p = 1) : d3255 p ≤ (0 : Int) + d37 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3255, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3255, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3255, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28450 p hg
    simpa only [d3255, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28452 (p : Pattern) (guard : d5268 p = 1) : d3256 p ≤ (0 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3256, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28449 p hg
    simpa only [d3256, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3256, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28451 p hg
    simpa only [d3256, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28453 (p : Pattern) (guard : d5268 p = 1) : d3258 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3258, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26654 p hg
    simpa only [d3258, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3258, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3258, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28454 (p : Pattern) (guard : d5268 p = 1) : d3259 p ≤ (0 : Int) + d42 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3259, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3259, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3259, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28453 p hg
    simpa only [d3259, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28455 (p : Pattern) (guard : d5268 p = 1) : d3260 p ≤ (0 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3260, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26626 p hg
    simpa only [d3260, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3260, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3260, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28456 (p : Pattern) (guard : d5268 p = 1) : d3261 p ≤ (0 : Int) + d44 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3261, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28454 p hg
    simpa only [d3261, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3261, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28455 p hg
    simpa only [d3261, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28457 (p : Pattern) (guard : d5268 p = 1) : d3262 p ≤ (0 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3262, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28452 p hg
    simpa only [d3262, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3262, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28456 p hg
    simpa only [d3262, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28458 (p : Pattern) (guard : d5268 p = 1) : d3263 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3263, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3263, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3263, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3263, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28459 (p : Pattern) (guard : d5268 p = 1) : d3264 p ≤ (0 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3264, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28458 p hg
    simpa only [d3264, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3264, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28455 p hg
    simpa only [d3264, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28460 (p : Pattern) (guard : d5268 p = 1) : d3265 p ≤ (0 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3265, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26635 p hg
    simpa only [d3265, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3265, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3265, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28461 (p : Pattern) (guard : d5268 p = 1) : d3266 p ≤ (0 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3266, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28460 p hg
    simpa only [d3266, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3266, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3266, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28462 (p : Pattern) (guard : d5268 p = 1) : d3267 p ≤ (0 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3267, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28459 p hg
    simpa only [d3267, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3267, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28461 p hg
    simpa only [d3267, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28463 (p : Pattern) (guard : d5268 p = 1) : d3268 p ≤ (0 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3268, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28457 p hg
    simpa only [d3268, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3268, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28462 p hg
    simpa only [d3268, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28464 (p : Pattern) (guard : d5268 p = 1) : d3269 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3269, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28447 p hg
    simpa only [d3269, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3269, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28463 p hg
    simpa only [d3269, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28465 (p : Pattern) (guard : d5268 p = 1) : d3272 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26671 p hg
    simpa only [d3272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28466 (p : Pattern) (guard : d5268 p = 1) : d3273 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28465 p hg
    simpa only [d3273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28467 (p : Pattern) (guard : d5268 p = 1) : d3274 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3274, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28466 p hg
    simpa only [d3274, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3274, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28432 p hg
    simpa only [d3274, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28468 (p : Pattern) (guard : d5268 p = 1) : d3275 p ≤ (0 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3275, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26643 p hg
    simpa only [d3275, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3275, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28448 p hg
    simpa only [d3275, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28469 (p : Pattern) (guard : d5268 p = 1) : d3276 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3276, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28467 p hg
    simpa only [d3276, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3276, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28468 p hg
    simpa only [d3276, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28470 (p : Pattern) (guard : d5268 p = 1) : d3277 p ≤ (0 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3277, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28440 p hg
    simpa only [d3277, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3277, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28444 p hg
    simpa only [d3277, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28471 (p : Pattern) (guard : d5268 p = 1) : d3278 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3278, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28469 p hg
    simpa only [d3278, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3278, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28470 p hg
    simpa only [d3278, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28472 (p : Pattern) (guard : d5268 p = 1) : d3280 p ≤ (0 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3280, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26680 p hg
    simpa only [d3280, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3280, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3280, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28473 (p : Pattern) (guard : d5268 p = 1) : d3281 p ≤ (0 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3281, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26680 p hg
    simpa only [d3281, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3281, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28472 p hg
    simpa only [d3281, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28474 (p : Pattern) (guard : d5268 p = 1) : d3282 p ≤ (0 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3282, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28440 p hg
    simpa only [d3282, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3282, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28473 p hg
    simpa only [d3282, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28475 (p : Pattern) (guard : d5268 p = 1) : d3283 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3283, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26654 p hg
    simpa only [d3283, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3283, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28453 p hg
    simpa only [d3283, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28476 (p : Pattern) (guard : d5268 p = 1) : d3284 p ≤ (0 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3284, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28475 p hg
    simpa only [d3284, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3284, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3284, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28477 (p : Pattern) (guard : d5268 p = 1) : d3285 p ≤ (0 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3285, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28474 p hg
    simpa only [d3285, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3285, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28476 p hg
    simpa only [d3285, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28478 (p : Pattern) (guard : d5268 p = 1) : d3286 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3286, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28471 p hg
    simpa only [d3286, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3286, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28477 p hg
    simpa only [d3286, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28479 (p : Pattern) (guard : d5268 p = 1) : d3287 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3287, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26643 p hg
    simpa only [d3287, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3287, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3287, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28480 (p : Pattern) (guard : d5268 p = 1) : d3288 p ≤ (0 : Int) + d67 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3288, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28451 p hg
    simpa only [d3288, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3288, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28479 p hg
    simpa only [d3288, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28481 (p : Pattern) (guard : d5268 p = 1) : d3289 p ≤ (0 : Int) + d68 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3289, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28455 p hg
    simpa only [d3289, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3289, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28460 p hg
    simpa only [d3289, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28482 (p : Pattern) (guard : d5268 p = 1) : d3290 p ≤ (0 : Int) + d69 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3290, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28480 p hg
    simpa only [d3290, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3290, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28481 p hg
    simpa only [d3290, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28483 (p : Pattern) (guard : d5268 p = 1) : d3291 p ≤ (0 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3291, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26680 p hg
    simpa only [d3291, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3291, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3291, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28484 (p : Pattern) (guard : d5268 p = 1) : d3292 p ≤ (0 : Int) + d71 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3292, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28455 p hg
    simpa only [d3292, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3292, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28483 p hg
    simpa only [d3292, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28485 (p : Pattern) (guard : d5268 p = 1) : d3293 p ≤ (0 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3293, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26654 p hg
    simpa only [d3293, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3293, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3293, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28486 (p : Pattern) (guard : d5268 p = 1) : d3294 p ≤ (0 : Int) + d73 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3294, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28485 p hg
    simpa only [d3294, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3294, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3294, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28487 (p : Pattern) (guard : d5268 p = 1) : d3295 p ≤ (0 : Int) + d74 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3295, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28484 p hg
    simpa only [d3295, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3295, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28486 p hg
    simpa only [d3295, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28488 (p : Pattern) (guard : d5268 p = 1) : d3296 p ≤ (0 : Int) + d75 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3296, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28482 p hg
    simpa only [d3296, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3296, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28487 p hg
    simpa only [d3296, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28489 (p : Pattern) (guard : d5268 p = 1) : d3297 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3297, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28478 p hg
    simpa only [d3297, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3297, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28488 p hg
    simpa only [d3297, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28490 (p : Pattern) (guard : d5268 p = 1) : d3298 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3298, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28464 p hg
    simpa only [d3298, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3298, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28489 p hg
    simpa only [d3298, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28491 (p : Pattern) (guard : d5268 p = 1) : d3299 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3299, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28438 p hg
    simpa only [d3299, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3299, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28441 p hg
    simpa only [d3299, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28492 (p : Pattern) (guard : d5268 p = 1) : d3300 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3300, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28491 p hg
    simpa only [d3300, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3300, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28446 p hg
    simpa only [d3300, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28493 (p : Pattern) (guard : d5268 p = 1) : d3301 p ≤ (0 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3301, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26648 p hg
    simpa only [d3301, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3301, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28450 p hg
    simpa only [d3301, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28494 (p : Pattern) (guard : d5268 p = 1) : d3302 p ≤ (0 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3302, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28468 p hg
    simpa only [d3302, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3302, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28493 p hg
    simpa only [d3302, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28495 (p : Pattern) (guard : d5268 p = 1) : d3303 p ≤ (0 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3303, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28494 p hg
    simpa only [d3303, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3303, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28476 p hg
    simpa only [d3303, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28496 (p : Pattern) (guard : d5268 p = 1) : d3304 p ≤ (0 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3304, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28495 p hg
    simpa only [d3304, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3304, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3304, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28497 (p : Pattern) (guard : d5268 p = 1) : d3305 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3305, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28492 p hg
    simpa only [d3305, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3305, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28496 p hg
    simpa only [d3305, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28498 (p : Pattern) (guard : d5268 p = 1) : d3306 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3306, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28438 p hg
    simpa only [d3306, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3306, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28468 p hg
    simpa only [d3306, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28499 (p : Pattern) (guard : d5268 p = 1) : d3307 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3307, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28498 p hg
    simpa only [d3307, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3307, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28470 p hg
    simpa only [d3307, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28500 (p : Pattern) (guard : d5268 p = 1) : d3308 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3308, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28499 p hg
    simpa only [d3308, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3308, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28477 p hg
    simpa only [d3308, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28501 (p : Pattern) (guard : d5268 p = 1) : d3309 p ≤ (0 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3309, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28493 p hg
    simpa only [d3309, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3309, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3309, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28502 (p : Pattern) (guard : d5268 p = 1) : d3310 p ≤ (0 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3310, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28501 p hg
    simpa only [d3310, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3310, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3310, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28503 (p : Pattern) (guard : d5268 p = 1) : d3311 p ≤ (0 : Int) + d85 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3311, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28502 p hg
    simpa only [d3311, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3311, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3311, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28504 (p : Pattern) (guard : d5268 p = 1) : d3312 p ≤ (0 : Int) + d86 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3312, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28500 p hg
    simpa only [d3312, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3312, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28503 p hg
    simpa only [d3312, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28505 (p : Pattern) (guard : d5268 p = 1) : d3313 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3313, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28497 p hg
    simpa only [d3313, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3313, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28504 p hg
    simpa only [d3313, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28506 (p : Pattern) (guard : d5268 p = 1) : d3314 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3314, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28490 p hg
    simpa only [d3314, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3314, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28505 p hg
    simpa only [d3314, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28507 (p : Pattern) (guard : d5268 p = 1) : d3315 p ≤ (0 : Int) + d89 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3315, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28444 p hg
    simpa only [d3315, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3315, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28475 p hg
    simpa only [d3315, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28508 (p : Pattern) (guard : d5268 p = 1) : d3316 p ≤ (0 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3316, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28507 p hg
    simpa only [d3316, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3316, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28476 p hg
    simpa only [d3316, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28509 (p : Pattern) (guard : d5268 p = 1) : d3317 p ≤ (0 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3317, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28476 p hg
    simpa only [d3317, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3317, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3317, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28510 (p : Pattern) (guard : d5268 p = 1) : d3318 p ≤ (0 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3318, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28508 p hg
    simpa only [d3318, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3318, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28509 p hg
    simpa only [d3318, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28511 (p : Pattern) (guard : d5268 p = 1) : d3319 p ≤ (0 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3319, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28509 p hg
    simpa only [d3319, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3319, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3319, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28512 (p : Pattern) (guard : d5268 p = 1) : d3320 p ≤ (0 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3320, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28510 p hg
    simpa only [d3320, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3320, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28511 p hg
    simpa only [d3320, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28513 (p : Pattern) (guard : d5268 p = 1) : d3321 p ≤ (0 : Int) + d95 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3321, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28511 p hg
    simpa only [d3321, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3321, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3321, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28514 (p : Pattern) (guard : d5268 p = 1) : d3322 p ≤ (0 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3322, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28512 p hg
    simpa only [d3322, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3322, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28513 p hg
    simpa only [d3322, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28515 (p : Pattern) (guard : d5268 p = 1) : d3323 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3323, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28505 p hg
    simpa only [d3323, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3323, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28514 p hg
    simpa only [d3323, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28516 (p : Pattern) (guard : d5268 p = 1) : d3324 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3324, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28506 p hg
    simpa only [d3324, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3324, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28515 p hg
    simpa only [d3324, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28517 (p : Pattern) (guard : d5268 p = 1) : d3325 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28436 p hg
    simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28438 p hg
    simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28518 (p : Pattern) (guard : d5268 p = 1) : d3326 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3326, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28517 p hg
    simpa only [d3326, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3326, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28441 p hg
    simpa only [d3326, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28519 (p : Pattern) (guard : d5268 p = 1) : d3327 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3327, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28518 p hg
    simpa only [d3327, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3327, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28446 p hg
    simpa only [d3327, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28520 (p : Pattern) (guard : d5268 p = 1) : d3328 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3328, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28519 p hg
    simpa only [d3328, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3328, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28463 p hg
    simpa only [d3328, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28521 (p : Pattern) (guard : d5268 p = 1) : d3329 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3329, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28500 p hg
    simpa only [d3329, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3329, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28488 p hg
    simpa only [d3329, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28522 (p : Pattern) (guard : d5268 p = 1) : d3330 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3330, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28520 p hg
    simpa only [d3330, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3330, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28521 p hg
    simpa only [d3330, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28523 (p : Pattern) (guard : d5268 p = 1) : d3331 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3331, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28522 p hg
    simpa only [d3331, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3331, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28505 p hg
    simpa only [d3331, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28524 (p : Pattern) (guard : d5268 p = 1) : d3332 p ≤ (0 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3332, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28505 p hg
    simpa only [d3332, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3332, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3332, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28525 (p : Pattern) (guard : d5268 p = 1) : d3333 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3333, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28523 p hg
    simpa only [d3333, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3333, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28524 p hg
    simpa only [d3333, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28526 (p : Pattern) (guard : d5268 p = 1) : d3334 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3334, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28516 p hg
    simpa only [d3334, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3334, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28525 p hg
    simpa only [d3334, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28527 (p : Pattern) (guard : d5268 p = 1) : d3337 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26745 p hg
    simpa only [d3337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28528 (p : Pattern) (guard : d5268 p = 1) : d3338 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28527 p hg
    simpa only [d3338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28529 (p : Pattern) (guard : d5268 p = 1) : d3339 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3339, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28528 p hg
    simpa only [d3339, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3339, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28432 p hg
    simpa only [d3339, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28530 (p : Pattern) (guard : d5268 p = 1) : d3340 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28529 p hg
    simpa only [d3340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28438 p hg
    simpa only [d3340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28531 (p : Pattern) (guard : d5268 p = 1) : d3341 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3341, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28530 p hg
    simpa only [d3341, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3341, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28441 p hg
    simpa only [d3341, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28532 (p : Pattern) (guard : d5268 p = 1) : d3342 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3342, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28531 p hg
    simpa only [d3342, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3342, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28446 p hg
    simpa only [d3342, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28533 (p : Pattern) (guard : d5268 p = 1) : d3343 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3343, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28532 p hg
    simpa only [d3343, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3343, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28463 p hg
    simpa only [d3343, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28534 (p : Pattern) (guard : d5268 p = 1) : d3344 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3344, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28436 p hg
    simpa only [d3344, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3344, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28468 p hg
    simpa only [d3344, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28535 (p : Pattern) (guard : d5268 p = 1) : d3345 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3345, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28534 p hg
    simpa only [d3345, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3345, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28470 p hg
    simpa only [d3345, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28536 (p : Pattern) (guard : d5268 p = 1) : d3346 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3346, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28535 p hg
    simpa only [d3346, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3346, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28477 p hg
    simpa only [d3346, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28537 (p : Pattern) (guard : d5268 p = 1) : d3347 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3347, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28536 p hg
    simpa only [d3347, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3347, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28488 p hg
    simpa only [d3347, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28538 (p : Pattern) (guard : d5268 p = 1) : d3348 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3348, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28533 p hg
    simpa only [d3348, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3348, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28537 p hg
    simpa only [d3348, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28539 (p : Pattern) (guard : d5268 p = 1) : d3349 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3349, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28538 p hg
    simpa only [d3349, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3349, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28505 p hg
    simpa only [d3349, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28540 (p : Pattern) (guard : d5268 p = 1) : d3350 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3350, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28539 p hg
    simpa only [d3350, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3350, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28515 p hg
    simpa only [d3350, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28541 (p : Pattern) (guard : d5268 p = 1) : d3351 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3351, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28492 p hg
    simpa only [d3351, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3351, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28463 p hg
    simpa only [d3351, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28542 (p : Pattern) (guard : d5268 p = 1) : d3352 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3352, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28541 p hg
    simpa only [d3352, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3352, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28521 p hg
    simpa only [d3352, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28543 (p : Pattern) (guard : d5268 p = 1) : d3353 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3353, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28542 p hg
    simpa only [d3353, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3353, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28505 p hg
    simpa only [d3353, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28544 (p : Pattern) (guard : d5268 p = 1) : d3354 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3354, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28543 p hg
    simpa only [d3354, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3354, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28524 p hg
    simpa only [d3354, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28545 (p : Pattern) (guard : d5268 p = 1) : d3355 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3355, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28540 p hg
    simpa only [d3355, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3355, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28544 p hg
    simpa only [d3355, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28546 (p : Pattern) (guard : d5268 p = 1) : d3356 p ≤ (0 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28526 p hg
    simpa only [d3356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28545 p hg
    simpa only [d3356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28547 (p : Pattern) (guard : d5268 p = 1) : d3360 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26771 p hg
    simpa only [d3360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26770 p hg
    simpa only [d3360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28548 (p : Pattern) (guard : d5268 p = 1) : d3361 p ≤ (0 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28547 p hg
    simpa only [d3361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26770 p hg
    simpa only [d3361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28549 (p : Pattern) (guard : d5268 p = 1) : d3362 p ≤ (0 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3362, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26770 p hg
    simpa only [d3362, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3362, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3362, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28550 (p : Pattern) (guard : d5268 p = 1) : d3363 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3363, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28548 p hg
    simpa only [d3363, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3363, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28549 p hg
    simpa only [d3363, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28551 (p : Pattern) (guard : d5268 p = 1) : d3364 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3364, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26770 p hg
    simpa only [d3364, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3364, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28549 p hg
    simpa only [d3364, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28552 (p : Pattern) (guard : d5268 p = 1) : d3365 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28550 p hg
    simpa only [d3365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28551 p hg
    simpa only [d3365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28553 (p : Pattern) (guard : d5268 p = 1) : d3367 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3367, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26785 p hg
    simpa only [d3367, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3367, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3367, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28554 (p : Pattern) (guard : d5268 p = 1) : d3368 p ≤ (0 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3368, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26785 p hg
    simpa only [d3368, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3368, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28553 p hg
    simpa only [d3368, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28555 (p : Pattern) (guard : d5268 p = 1) : d3369 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3369, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28551 p hg
    simpa only [d3369, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3369, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28554 p hg
    simpa only [d3369, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28556 (p : Pattern) (guard : d5268 p = 1) : d3370 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3370, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28552 p hg
    simpa only [d3370, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3370, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28555 p hg
    simpa only [d3370, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28557 (p : Pattern) (guard : d5268 p = 1) : d3371 p ≤ (0 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3371, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28473 p hg
    simpa only [d3371, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3371, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3371, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28558 (p : Pattern) (guard : d5268 p = 1) : d3372 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3372, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28555 p hg
    simpa only [d3372, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3372, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28557 p hg
    simpa only [d3372, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28559 (p : Pattern) (guard : d5268 p = 1) : d3373 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3373, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28556 p hg
    simpa only [d3373, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3373, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28558 p hg
    simpa only [d3373, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
