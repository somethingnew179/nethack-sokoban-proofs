/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons125
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare17640 (p : Pattern) (guard : d5537 p = 1) : d2183 p ≤ (0 : Int) + d2894 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2183, d2894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17457 p hg
    simpa only [d2183, d2894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2183, d2894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17639 p hg
    simpa only [d2183, d2894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17641 (p : Pattern) (guard : d5538 p = 1) : d267 p ≤ (0 : Int) + d267 p := by
  omega
theorem compare17642 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d190 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17643 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3225 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d14, d3225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5268, d14, d3225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d14, d3225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17642 p hg
    simpa only [d5268, d14, d3225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17644 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17645 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d14, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5268, d14, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d14, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5268, d14, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17646 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3227 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17643 p hg
    simpa only [d3227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d3227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17647 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3228 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17646 p hg
    simpa only [d3228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d3228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17648 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3229 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17647 p hg
    simpa only [d3229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d3229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17649 (p : Pattern) (guard : d5268 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare17650 (p : Pattern) (guard : d5268 p = 1) : d15 p ≤ (0 : Int) + d3230 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d15, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d15, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d15, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d15, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17651 (p : Pattern) (guard : d5268 p = 1) : d16 p ≤ (0 : Int) + d3231 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d16, d3231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17648 p hg
    simpa only [d16, d3231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d16, d3231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17650 p hg
    simpa only [d16, d3231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17652 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d39 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17653 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3232 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d14, d3232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5268, d14, d3232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d14, d3232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17652 p hg
    simpa only [d5268, d14, d3232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17654 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3233 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17653 p hg
    simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17655 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3234 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17654 p hg
    simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17656 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3235 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17655 p hg
    simpa only [d3235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d3235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17657 (p : Pattern) (guard : d5268 p = 1) : d16 p ≤ (0 : Int) + d3236 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d16, d3236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17656 p hg
    simpa only [d16, d3236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d16, d3236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17650 p hg
    simpa only [d16, d3236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17658 (p : Pattern) (guard : d5268 p = 1) : d16 p ≤ (0 : Int) + d3237 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17651 p hg
    simpa only [d3237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17657 p hg
    simpa only [d3237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17659 (p : Pattern) (guard : d5268 p = 1) : d16 p ≤ (0 : Int) + d3238 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d16, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d16, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d16, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17650 p hg
    simpa only [d16, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17660 (p : Pattern) (guard : d0 p = 1) : d17 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17661 (p : Pattern) (guard : d5268 p = 1) : d18 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d18, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d5268, d18, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d18, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5268, d18, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17662 (p : Pattern) (guard : d5268 p = 1) : d19 p ≤ (0 : Int) + d3240 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d19, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17661 p hg
    simpa only [d19, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d19, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d19, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17663 (p : Pattern) (guard : d5268 p = 1) : d20 p ≤ (0 : Int) + d3241 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d20, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17661 p hg
    simpa only [d20, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d20, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17662 p hg
    simpa only [d20, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17664 (p : Pattern) (guard : d5268 p = 1) : d21 p ≤ (0 : Int) + d3242 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d21, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17659 p hg
    simpa only [d21, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d21, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17663 p hg
    simpa only [d21, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17665 (p : Pattern) (guard : d5268 p = 1) : d22 p ≤ (0 : Int) + d3243 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d22, d3243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17658 p hg
    simpa only [d22, d3243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d22, d3243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17664 p hg
    simpa only [d22, d3243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17666 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17667 (p : Pattern) (guard : d5268 p = 1) : d24 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d24, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14547 p hg
    simpa only [d5268, d24, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d24, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5268, d24, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17668 (p : Pattern) (guard : d5268 p = 1) : d25 p ≤ (0 : Int) + d3245 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d25, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17667 p hg
    simpa only [d25, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d25, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d25, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17669 (p : Pattern) (guard : d5268 p = 1) : d26 p ≤ (0 : Int) + d3246 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d26, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17667 p hg
    simpa only [d26, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d26, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17668 p hg
    simpa only [d26, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17670 (p : Pattern) (guard : d5268 p = 1) : d27 p ≤ (0 : Int) + d3247 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d27, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17669 p hg
    simpa only [d27, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d27, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d27, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17671 (p : Pattern) (guard : d5268 p = 1) : d28 p ≤ (0 : Int) + d3248 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d28, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17664 p hg
    simpa only [d28, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d28, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17670 p hg
    simpa only [d28, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17672 (p : Pattern) (guard : d5268 p = 1) : d29 p ≤ (0 : Int) + d3249 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d29, d3249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17665 p hg
    simpa only [d29, d3249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d29, d3249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17671 p hg
    simpa only [d29, d3249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17673 (p : Pattern) (guard : d0 p = 1) : d30 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17674 (p : Pattern) (guard : d5268 p = 1) : d31 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d31, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d5268, d31, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d31, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5268, d31, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17675 (p : Pattern) (guard : d5268 p = 1) : d32 p ≤ (0 : Int) + d3251 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d32, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17674 p hg
    simpa only [d32, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d32, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d32, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17676 (p : Pattern) (guard : d5268 p = 1) : d33 p ≤ (0 : Int) + d3252 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d33, d3252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d33, d3252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d33, d3252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17675 p hg
    simpa only [d33, d3252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17677 (p : Pattern) (guard : d0 p = 1) : d34 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17678 (p : Pattern) (guard : d5268 p = 1) : d35 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d35, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14566 p hg
    simpa only [d5268, d35, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d35, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5268, d35, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17679 (p : Pattern) (guard : d5268 p = 1) : d36 p ≤ (0 : Int) + d3254 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d36, d3254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17678 p hg
    simpa only [d36, d3254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d36, d3254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d36, d3254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17680 (p : Pattern) (guard : d5268 p = 1) : d37 p ≤ (0 : Int) + d3255 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d37, d3255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d37, d3255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d37, d3255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17679 p hg
    simpa only [d37, d3255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17681 (p : Pattern) (guard : d5268 p = 1) : d38 p ≤ (0 : Int) + d3256 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d38, d3256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17676 p hg
    simpa only [d38, d3256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d38, d3256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17680 p hg
    simpa only [d38, d3256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17682 (p : Pattern) (guard : d0 p = 1) : d39 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17683 (p : Pattern) (guard : d5268 p = 1) : d40 p ≤ (0 : Int) + d3257 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d40, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14575 p hg
    simpa only [d5268, d40, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d40, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5268, d40, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17684 (p : Pattern) (guard : d5268 p = 1) : d41 p ≤ (0 : Int) + d3258 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d41, d3258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17683 p hg
    simpa only [d41, d3258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d41, d3258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d41, d3258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17685 (p : Pattern) (guard : d5268 p = 1) : d42 p ≤ (0 : Int) + d3259 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d42, d3259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d42, d3259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d42, d3259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17684 p hg
    simpa only [d42, d3259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17686 (p : Pattern) (guard : d5268 p = 1) : d43 p ≤ (0 : Int) + d3260 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d43, d3260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17661 p hg
    simpa only [d43, d3260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d43, d3260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d43, d3260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17687 (p : Pattern) (guard : d5268 p = 1) : d44 p ≤ (0 : Int) + d3261 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d44, d3261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17685 p hg
    simpa only [d44, d3261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d44, d3261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17686 p hg
    simpa only [d44, d3261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17688 (p : Pattern) (guard : d5268 p = 1) : d45 p ≤ (0 : Int) + d3262 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d45, d3262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17681 p hg
    simpa only [d45, d3262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d45, d3262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17687 p hg
    simpa only [d45, d3262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17689 (p : Pattern) (guard : d5268 p = 1) : d46 p ≤ (0 : Int) + d3263 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d46, d3263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d46, d3263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d46, d3263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d46, d3263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17690 (p : Pattern) (guard : d5268 p = 1) : d47 p ≤ (0 : Int) + d3264 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d47, d3264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17689 p hg
    simpa only [d47, d3264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d47, d3264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17686 p hg
    simpa only [d47, d3264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17691 (p : Pattern) (guard : d5268 p = 1) : d48 p ≤ (0 : Int) + d3265 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d48, d3265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17667 p hg
    simpa only [d48, d3265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d48, d3265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d48, d3265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17692 (p : Pattern) (guard : d5268 p = 1) : d49 p ≤ (0 : Int) + d3266 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d49, d3266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17691 p hg
    simpa only [d49, d3266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d49, d3266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d49, d3266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17693 (p : Pattern) (guard : d5268 p = 1) : d50 p ≤ (0 : Int) + d3267 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d50, d3267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17690 p hg
    simpa only [d50, d3267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d50, d3267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17692 p hg
    simpa only [d50, d3267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17694 (p : Pattern) (guard : d5268 p = 1) : d51 p ≤ (0 : Int) + d3268 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d51, d3268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17688 p hg
    simpa only [d51, d3268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d51, d3268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17693 p hg
    simpa only [d51, d3268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17695 (p : Pattern) (guard : d5268 p = 1) : d52 p ≤ (0 : Int) + d3269 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d52, d3269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17672 p hg
    simpa only [d52, d3269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d52, d3269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17694 p hg
    simpa only [d52, d3269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17696 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17697 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3270 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d14, d3270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5268, d14, d3270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d14, d3270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17696 p hg
    simpa only [d5268, d14, d3270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17698 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3271 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17697 p hg
    simpa only [d3271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d3271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17699 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3272 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17698 p hg
    simpa only [d3272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d3272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17700 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3273 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17699 p hg
    simpa only [d3273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d3273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17701 (p : Pattern) (guard : d5268 p = 1) : d16 p ≤ (0 : Int) + d3274 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d16, d3274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17700 p hg
    simpa only [d16, d3274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d16, d3274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17650 p hg
    simpa only [d16, d3274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17702 (p : Pattern) (guard : d5268 p = 1) : d53 p ≤ (0 : Int) + d3275 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d53, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17674 p hg
    simpa only [d53, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d53, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17675 p hg
    simpa only [d53, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17703 (p : Pattern) (guard : d5268 p = 1) : d54 p ≤ (0 : Int) + d3276 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d54, d3276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17701 p hg
    simpa only [d54, d3276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d54, d3276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17702 p hg
    simpa only [d54, d3276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17704 (p : Pattern) (guard : d5268 p = 1) : d55 p ≤ (0 : Int) + d3277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d55, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17663 p hg
    simpa only [d55, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d55, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17669 p hg
    simpa only [d55, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17705 (p : Pattern) (guard : d5268 p = 1) : d56 p ≤ (0 : Int) + d3278 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d56, d3278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17703 p hg
    simpa only [d56, d3278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d56, d3278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17704 p hg
    simpa only [d56, d3278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17706 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17707 (p : Pattern) (guard : d5268 p = 1) : d58 p ≤ (0 : Int) + d3279 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d58, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14597 p hg
    simpa only [d5268, d58, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d58, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5268, d58, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17708 (p : Pattern) (guard : d5268 p = 1) : d59 p ≤ (0 : Int) + d3280 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d59, d3280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17707 p hg
    simpa only [d59, d3280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d59, d3280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d59, d3280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17709 (p : Pattern) (guard : d5268 p = 1) : d60 p ≤ (0 : Int) + d3281 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d60, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17707 p hg
    simpa only [d60, d3281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d60, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17708 p hg
    simpa only [d60, d3281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17710 (p : Pattern) (guard : d5268 p = 1) : d61 p ≤ (0 : Int) + d3282 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d61, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17663 p hg
    simpa only [d61, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d61, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17709 p hg
    simpa only [d61, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17711 (p : Pattern) (guard : d5268 p = 1) : d62 p ≤ (0 : Int) + d3283 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d62, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17683 p hg
    simpa only [d62, d3283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d62, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17684 p hg
    simpa only [d62, d3283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17712 (p : Pattern) (guard : d5268 p = 1) : d63 p ≤ (0 : Int) + d3284 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d63, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17711 p hg
    simpa only [d63, d3284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d63, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d63, d3284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17713 (p : Pattern) (guard : d5268 p = 1) : d64 p ≤ (0 : Int) + d3285 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d64, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17710 p hg
    simpa only [d64, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d64, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17712 p hg
    simpa only [d64, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17714 (p : Pattern) (guard : d5268 p = 1) : d65 p ≤ (0 : Int) + d3286 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d65, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17705 p hg
    simpa only [d65, d3286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d65, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17713 p hg
    simpa only [d65, d3286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17715 (p : Pattern) (guard : d5268 p = 1) : d66 p ≤ (0 : Int) + d3287 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d66, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17674 p hg
    simpa only [d66, d3287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d66, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d66, d3287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17716 (p : Pattern) (guard : d5268 p = 1) : d67 p ≤ (0 : Int) + d3288 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d67, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17680 p hg
    simpa only [d67, d3288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d67, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17715 p hg
    simpa only [d67, d3288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17717 (p : Pattern) (guard : d5268 p = 1) : d68 p ≤ (0 : Int) + d3289 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d68, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17686 p hg
    simpa only [d68, d3289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d68, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17691 p hg
    simpa only [d68, d3289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17718 (p : Pattern) (guard : d5268 p = 1) : d69 p ≤ (0 : Int) + d3290 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d69, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17716 p hg
    simpa only [d69, d3290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d69, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17717 p hg
    simpa only [d69, d3290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17719 (p : Pattern) (guard : d5268 p = 1) : d70 p ≤ (0 : Int) + d3291 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d70, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17707 p hg
    simpa only [d70, d3291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d70, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d70, d3291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17720 (p : Pattern) (guard : d5268 p = 1) : d71 p ≤ (0 : Int) + d3292 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d71, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17686 p hg
    simpa only [d71, d3292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d71, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17719 p hg
    simpa only [d71, d3292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17721 (p : Pattern) (guard : d5268 p = 1) : d72 p ≤ (0 : Int) + d3293 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d72, d3293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17683 p hg
    simpa only [d72, d3293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d72, d3293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d72, d3293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17722 (p : Pattern) (guard : d5268 p = 1) : d73 p ≤ (0 : Int) + d3294 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d73, d3294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17721 p hg
    simpa only [d73, d3294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d73, d3294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d73, d3294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17723 (p : Pattern) (guard : d5268 p = 1) : d74 p ≤ (0 : Int) + d3295 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d74, d3295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17720 p hg
    simpa only [d74, d3295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d74, d3295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17722 p hg
    simpa only [d74, d3295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17724 (p : Pattern) (guard : d5268 p = 1) : d75 p ≤ (0 : Int) + d3296 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d75, d3296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17718 p hg
    simpa only [d75, d3296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d75, d3296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17723 p hg
    simpa only [d75, d3296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17725 (p : Pattern) (guard : d5268 p = 1) : d76 p ≤ (0 : Int) + d3297 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d76, d3297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17714 p hg
    simpa only [d76, d3297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d76, d3297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17724 p hg
    simpa only [d76, d3297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17726 (p : Pattern) (guard : d5268 p = 1) : d77 p ≤ (0 : Int) + d3298 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d77, d3298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17695 p hg
    simpa only [d77, d3298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d77, d3298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17725 p hg
    simpa only [d77, d3298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17727 (p : Pattern) (guard : d5268 p = 1) : d22 p ≤ (0 : Int) + d3299 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d22, d3299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17659 p hg
    simpa only [d22, d3299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d22, d3299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17664 p hg
    simpa only [d22, d3299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17728 (p : Pattern) (guard : d5268 p = 1) : d29 p ≤ (0 : Int) + d3300 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d29, d3300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17727 p hg
    simpa only [d29, d3300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d29, d3300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17671 p hg
    simpa only [d29, d3300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17729 (p : Pattern) (guard : d5268 p = 1) : d78 p ≤ (0 : Int) + d3301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d78, d3301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17678 p hg
    simpa only [d78, d3301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d78, d3301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17679 p hg
    simpa only [d78, d3301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17730 (p : Pattern) (guard : d5268 p = 1) : d79 p ≤ (0 : Int) + d3302 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d79, d3302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17702 p hg
    simpa only [d79, d3302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d79, d3302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17729 p hg
    simpa only [d79, d3302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17731 (p : Pattern) (guard : d5268 p = 1) : d80 p ≤ (0 : Int) + d3303 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d80, d3303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17730 p hg
    simpa only [d80, d3303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d80, d3303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17712 p hg
    simpa only [d80, d3303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17732 (p : Pattern) (guard : d5268 p = 1) : d81 p ≤ (0 : Int) + d3304 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d81, d3304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17731 p hg
    simpa only [d81, d3304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d81, d3304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d81, d3304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17733 (p : Pattern) (guard : d5268 p = 1) : d82 p ≤ (0 : Int) + d3305 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d82, d3305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17728 p hg
    simpa only [d82, d3305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d82, d3305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17732 p hg
    simpa only [d82, d3305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17734 (p : Pattern) (guard : d5268 p = 1) : d54 p ≤ (0 : Int) + d3306 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d54, d3306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17659 p hg
    simpa only [d54, d3306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d54, d3306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17702 p hg
    simpa only [d54, d3306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17735 (p : Pattern) (guard : d5268 p = 1) : d56 p ≤ (0 : Int) + d3307 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d56, d3307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17734 p hg
    simpa only [d56, d3307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d56, d3307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17704 p hg
    simpa only [d56, d3307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17736 (p : Pattern) (guard : d5268 p = 1) : d65 p ≤ (0 : Int) + d3308 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d65, d3308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17735 p hg
    simpa only [d65, d3308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d65, d3308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17713 p hg
    simpa only [d65, d3308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17737 (p : Pattern) (guard : d5268 p = 1) : d83 p ≤ (0 : Int) + d3309 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d83, d3309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17729 p hg
    simpa only [d83, d3309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d83, d3309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d83, d3309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17738 (p : Pattern) (guard : d5268 p = 1) : d84 p ≤ (0 : Int) + d3310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d84, d3310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17737 p hg
    simpa only [d84, d3310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d84, d3310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d84, d3310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17739 (p : Pattern) (guard : d5268 p = 1) : d85 p ≤ (0 : Int) + d3311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d85, d3311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17738 p hg
    simpa only [d85, d3311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d85, d3311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d85, d3311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17740 (p : Pattern) (guard : d5268 p = 1) : d86 p ≤ (0 : Int) + d3312 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d86, d3312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17736 p hg
    simpa only [d86, d3312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d86, d3312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17739 p hg
    simpa only [d86, d3312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17741 (p : Pattern) (guard : d5268 p = 1) : d87 p ≤ (0 : Int) + d3313 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d87, d3313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17733 p hg
    simpa only [d87, d3313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d87, d3313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17740 p hg
    simpa only [d87, d3313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17742 (p : Pattern) (guard : d5268 p = 1) : d88 p ≤ (0 : Int) + d3314 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d88, d3314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17726 p hg
    simpa only [d88, d3314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d88, d3314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17741 p hg
    simpa only [d88, d3314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17743 (p : Pattern) (guard : d5268 p = 1) : d89 p ≤ (0 : Int) + d3315 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d89, d3315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17669 p hg
    simpa only [d89, d3315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d89, d3315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17711 p hg
    simpa only [d89, d3315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17744 (p : Pattern) (guard : d5268 p = 1) : d90 p ≤ (0 : Int) + d3316 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d90, d3316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17743 p hg
    simpa only [d90, d3316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d90, d3316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17712 p hg
    simpa only [d90, d3316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17745 (p : Pattern) (guard : d5268 p = 1) : d91 p ≤ (0 : Int) + d3317 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d91, d3317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17712 p hg
    simpa only [d91, d3317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d91, d3317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d91, d3317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17746 (p : Pattern) (guard : d5268 p = 1) : d92 p ≤ (0 : Int) + d3318 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d92, d3318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17744 p hg
    simpa only [d92, d3318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d92, d3318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17745 p hg
    simpa only [d92, d3318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17747 (p : Pattern) (guard : d5268 p = 1) : d93 p ≤ (0 : Int) + d3319 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d93, d3319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17745 p hg
    simpa only [d93, d3319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d93, d3319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d93, d3319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17748 (p : Pattern) (guard : d5268 p = 1) : d94 p ≤ (0 : Int) + d3320 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d94, d3320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17746 p hg
    simpa only [d94, d3320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d94, d3320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17747 p hg
    simpa only [d94, d3320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17749 (p : Pattern) (guard : d5268 p = 1) : d95 p ≤ (0 : Int) + d3321 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d95, d3321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17747 p hg
    simpa only [d95, d3321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d95, d3321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d95, d3321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17750 (p : Pattern) (guard : d5268 p = 1) : d96 p ≤ (0 : Int) + d3322 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d96, d3322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17748 p hg
    simpa only [d96, d3322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d96, d3322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17749 p hg
    simpa only [d96, d3322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17751 (p : Pattern) (guard : d5268 p = 1) : d97 p ≤ (0 : Int) + d3323 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d97, d3323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17741 p hg
    simpa only [d97, d3323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d97, d3323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17750 p hg
    simpa only [d97, d3323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17752 (p : Pattern) (guard : d5268 p = 1) : d98 p ≤ (0 : Int) + d3324 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d98, d3324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17742 p hg
    simpa only [d98, d3324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d98, d3324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17751 p hg
    simpa only [d98, d3324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17753 (p : Pattern) (guard : d5268 p = 1) : d16 p ≤ (0 : Int) + d3325 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17657 p hg
    simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17659 p hg
    simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17754 (p : Pattern) (guard : d5268 p = 1) : d22 p ≤ (0 : Int) + d3326 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d22, d3326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17753 p hg
    simpa only [d22, d3326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d22, d3326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17664 p hg
    simpa only [d22, d3326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17755 (p : Pattern) (guard : d5268 p = 1) : d29 p ≤ (0 : Int) + d3327 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d29, d3327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17754 p hg
    simpa only [d29, d3327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d29, d3327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17671 p hg
    simpa only [d29, d3327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17756 (p : Pattern) (guard : d5268 p = 1) : d52 p ≤ (0 : Int) + d3328 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d52, d3328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17755 p hg
    simpa only [d52, d3328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d52, d3328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17694 p hg
    simpa only [d52, d3328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17757 (p : Pattern) (guard : d5268 p = 1) : d76 p ≤ (0 : Int) + d3329 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d76, d3329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17736 p hg
    simpa only [d76, d3329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d76, d3329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17724 p hg
    simpa only [d76, d3329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17758 (p : Pattern) (guard : d5268 p = 1) : d77 p ≤ (0 : Int) + d3330 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d77, d3330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17756 p hg
    simpa only [d77, d3330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d77, d3330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17757 p hg
    simpa only [d77, d3330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17759 (p : Pattern) (guard : d5268 p = 1) : d88 p ≤ (0 : Int) + d3331 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d88, d3331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17758 p hg
    simpa only [d88, d3331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d88, d3331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17741 p hg
    simpa only [d88, d3331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17760 (p : Pattern) (guard : d5268 p = 1) : d99 p ≤ (0 : Int) + d3332 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d99, d3332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17741 p hg
    simpa only [d99, d3332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d99, d3332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d99, d3332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17761 (p : Pattern) (guard : d5268 p = 1) : d100 p ≤ (0 : Int) + d3333 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d100, d3333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17759 p hg
    simpa only [d100, d3333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d100, d3333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17760 p hg
    simpa only [d100, d3333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17762 (p : Pattern) (guard : d5268 p = 1) : d101 p ≤ (0 : Int) + d3334 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d101, d3334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17752 p hg
    simpa only [d101, d3334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d101, d3334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17761 p hg
    simpa only [d101, d3334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17763 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17764 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3335 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d14, d3335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5268, d14, d3335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d14, d3335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17763 p hg
    simpa only [d5268, d14, d3335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17765 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3336 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17764 p hg
    simpa only [d3336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d3336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17766 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3337 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17765 p hg
    simpa only [d3337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d3337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17767 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d3338 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17766 p hg
    simpa only [d3338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d3338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17768 (p : Pattern) (guard : d5268 p = 1) : d16 p ≤ (0 : Int) + d3339 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d16, d3339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17767 p hg
    simpa only [d16, d3339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d16, d3339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17650 p hg
    simpa only [d16, d3339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17769 (p : Pattern) (guard : d5268 p = 1) : d16 p ≤ (0 : Int) + d3340 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17768 p hg
    simpa only [d3340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17659 p hg
    simpa only [d3340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17770 (p : Pattern) (guard : d5268 p = 1) : d22 p ≤ (0 : Int) + d3341 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d22, d3341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17769 p hg
    simpa only [d22, d3341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d22, d3341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17664 p hg
    simpa only [d22, d3341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17771 (p : Pattern) (guard : d5268 p = 1) : d29 p ≤ (0 : Int) + d3342 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d29, d3342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17770 p hg
    simpa only [d29, d3342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d29, d3342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17671 p hg
    simpa only [d29, d3342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17772 (p : Pattern) (guard : d5268 p = 1) : d52 p ≤ (0 : Int) + d3343 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d52, d3343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17771 p hg
    simpa only [d52, d3343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d52, d3343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17694 p hg
    simpa only [d52, d3343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17773 (p : Pattern) (guard : d5268 p = 1) : d54 p ≤ (0 : Int) + d3344 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d54, d3344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17657 p hg
    simpa only [d54, d3344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d54, d3344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17702 p hg
    simpa only [d54, d3344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17774 (p : Pattern) (guard : d5268 p = 1) : d56 p ≤ (0 : Int) + d3345 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d56, d3345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17773 p hg
    simpa only [d56, d3345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d56, d3345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17704 p hg
    simpa only [d56, d3345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17775 (p : Pattern) (guard : d5268 p = 1) : d65 p ≤ (0 : Int) + d3346 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d65, d3346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17774 p hg
    simpa only [d65, d3346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d65, d3346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17713 p hg
    simpa only [d65, d3346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17776 (p : Pattern) (guard : d5268 p = 1) : d76 p ≤ (0 : Int) + d3347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d76, d3347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17775 p hg
    simpa only [d76, d3347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d76, d3347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17724 p hg
    simpa only [d76, d3347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17777 (p : Pattern) (guard : d5268 p = 1) : d77 p ≤ (0 : Int) + d3348 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d77, d3348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17772 p hg
    simpa only [d77, d3348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d77, d3348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17776 p hg
    simpa only [d77, d3348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17778 (p : Pattern) (guard : d5268 p = 1) : d88 p ≤ (0 : Int) + d3349 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d88, d3349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17777 p hg
    simpa only [d88, d3349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d88, d3349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17741 p hg
    simpa only [d88, d3349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17779 (p : Pattern) (guard : d5268 p = 1) : d98 p ≤ (0 : Int) + d3350 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d98, d3350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17778 p hg
    simpa only [d98, d3350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d98, d3350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17751 p hg
    simpa only [d98, d3350, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
