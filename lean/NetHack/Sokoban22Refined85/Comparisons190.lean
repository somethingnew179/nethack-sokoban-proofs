/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons189
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare26600 (p : Pattern) (guard : d6326 p = 1) : d265 p ≤ (0 : Int) + d6555 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d265, d6555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26428 p hg
    simpa only [d265, d6555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d265, d6555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26599 p hg
    simpa only [d265, d6555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26601 (p : Pattern) (guard : d6326 p = 1) : d266 p ≤ (0 : Int) + d6556 p := by
  cases selected : p 49 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d266, d6556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26545 p hg
    simpa only [d266, d6556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d266, d6556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26600 p hg
    simpa only [d266, d6556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26602 (p : Pattern) (guard : d6326 p = 1) : d267 p ≤ (0 : Int) + d6557 p := by
  cases selected : p 48 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d267, d6557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26504 p hg
    simpa only [d267, d6557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d267, d6557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26601 p hg
    simpa only [d267, d6557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26603 (p : Pattern) (guard : d0 p = 1) : d190 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26604 (p : Pattern) (guard : d5268 p = 1) : d3225 p ≤ (0 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3225, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5268, d3225, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3225, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26603 p hg
    simpa only [d5268, d3225, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26605 (p : Pattern) (guard : d5268 p = 1) : d3226 p ≤ (0 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3226, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5268, d3226, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3226, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19882 p hg
    simpa only [d5268, d3226, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26606 (p : Pattern) (guard : d5268 p = 1) : d3227 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26604 p hg
    simpa only [d3227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26607 (p : Pattern) (guard : d0 p = 1) : d3226 p ≤ (0 : Int) + d318 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26608 (p : Pattern) (guard : d5539 p = 1) : d3228 p ≤ (0 : Int) + d2184 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d3228, d2184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26606 p hg
    simpa only [d5539, d3228, d2184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d3228, d2184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26607 p hg
    simpa only [d5539, d3228, d2184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26609 (p : Pattern) (guard : d0 p = 1) : d3226 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26610 (p : Pattern) (guard : d5539 p = 1) : d3226 p ≤ (0 : Int) + d2185 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d5539, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d5539, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26611 (p : Pattern) (guard : d5539 p = 1) : d3229 p ≤ (0 : Int) + d2186 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3229, d2186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26608 p hg
    simpa only [d3229, d2186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3229, d2186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26610 p hg
    simpa only [d3229, d2186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26612 (p : Pattern) (guard : d5539 p = 1) : d3230 p ≤ (0 : Int) + d2187 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3230, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26610 p hg
    simpa only [d3230, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3230, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3230, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26613 (p : Pattern) (guard : d5539 p = 1) : d3231 p ≤ (0 : Int) + d2188 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3231, d2188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26611 p hg
    simpa only [d3231, d2188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3231, d2188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26612 p hg
    simpa only [d3231, d2188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26614 (p : Pattern) (guard : d0 p = 1) : d39 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26615 (p : Pattern) (guard : d5268 p = 1) : d3232 p ≤ (0 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3232, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5268, d3232, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3232, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26614 p hg
    simpa only [d5268, d3232, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26616 (p : Pattern) (guard : d5268 p = 1) : d3233 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26615 p hg
    simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26617 (p : Pattern) (guard : d0 p = 1) : d3226 p ≤ (0 : Int) + d330 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26618 (p : Pattern) (guard : d5539 p = 1) : d3234 p ≤ (0 : Int) + d2189 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d3234, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26616 p hg
    simpa only [d5539, d3234, d2189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d3234, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26617 p hg
    simpa only [d5539, d3234, d2189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26619 (p : Pattern) (guard : d5539 p = 1) : d3235 p ≤ (0 : Int) + d2190 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3235, d2190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26618 p hg
    simpa only [d3235, d2190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3235, d2190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26610 p hg
    simpa only [d3235, d2190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26620 (p : Pattern) (guard : d5539 p = 1) : d3236 p ≤ (0 : Int) + d2191 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3236, d2191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26619 p hg
    simpa only [d3236, d2191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3236, d2191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26612 p hg
    simpa only [d3236, d2191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26621 (p : Pattern) (guard : d5539 p = 1) : d3237 p ≤ (0 : Int) + d2192 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3237, d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26613 p hg
    simpa only [d3237, d2192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3237, d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26620 p hg
    simpa only [d3237, d2192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26622 (p : Pattern) (guard : d0 p = 1) : d3226 p ≤ (0 : Int) + d332 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26623 (p : Pattern) (guard : d5539 p = 1) : d3226 p ≤ (0 : Int) + d2193 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d5539, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26622 p hg
    simpa only [d5539, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26624 (p : Pattern) (guard : d5539 p = 1) : d3226 p ≤ (0 : Int) + d2194 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26623 p hg
    simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26610 p hg
    simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26625 (p : Pattern) (guard : d5539 p = 1) : d3238 p ≤ (0 : Int) + d2195 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3238, d2195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26624 p hg
    simpa only [d3238, d2195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3238, d2195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26612 p hg
    simpa only [d3238, d2195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26626 (p : Pattern) (guard : d5268 p = 1) : d3239 p ≤ (0 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3239, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d5268, d3239, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3239, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19865 p hg
    simpa only [d5268, d3239, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26627 (p : Pattern) (guard : d0 p = 1) : d3239 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26628 (p : Pattern) (guard : d5539 p = 1) : d3239 p ≤ (0 : Int) + d2196 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26626 p hg
    simpa only [d5539, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d5539, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26629 (p : Pattern) (guard : d5539 p = 1) : d3240 p ≤ (0 : Int) + d2197 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3240, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26628 p hg
    simpa only [d3240, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3240, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3240, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26630 (p : Pattern) (guard : d5539 p = 1) : d3241 p ≤ (0 : Int) + d2198 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3241, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26628 p hg
    simpa only [d3241, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3241, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26629 p hg
    simpa only [d3241, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26631 (p : Pattern) (guard : d5539 p = 1) : d3242 p ≤ (0 : Int) + d2199 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3242, d2199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26625 p hg
    simpa only [d3242, d2199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3242, d2199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26630 p hg
    simpa only [d3242, d2199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26632 (p : Pattern) (guard : d5539 p = 1) : d3243 p ≤ (0 : Int) + d2200 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3243, d2200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26621 p hg
    simpa only [d3243, d2200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3243, d2200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26631 p hg
    simpa only [d3243, d2200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26633 (p : Pattern) (guard : d5539 p = 1) : d3238 p ≤ (0 : Int) + d2201 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3238, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26610 p hg
    simpa only [d3238, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3238, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26612 p hg
    simpa only [d3238, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26634 (p : Pattern) (guard : d5539 p = 1) : d3242 p ≤ (0 : Int) + d2202 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3242, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26633 p hg
    simpa only [d3242, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3242, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26630 p hg
    simpa only [d3242, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26635 (p : Pattern) (guard : d5268 p = 1) : d3244 p ≤ (0 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3244, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14547 p hg
    simpa only [d5268, d3244, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3244, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19893 p hg
    simpa only [d5268, d3244, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26636 (p : Pattern) (guard : d0 p = 1) : d3244 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26637 (p : Pattern) (guard : d5539 p = 1) : d3244 p ≤ (0 : Int) + d2203 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26635 p hg
    simpa only [d5539, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26636 p hg
    simpa only [d5539, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26638 (p : Pattern) (guard : d5539 p = 1) : d3245 p ≤ (0 : Int) + d2204 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3245, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26637 p hg
    simpa only [d3245, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3245, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3245, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26639 (p : Pattern) (guard : d5539 p = 1) : d3246 p ≤ (0 : Int) + d2205 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3246, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26637 p hg
    simpa only [d3246, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3246, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26638 p hg
    simpa only [d3246, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26640 (p : Pattern) (guard : d5539 p = 1) : d3247 p ≤ (0 : Int) + d2206 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3247, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26639 p hg
    simpa only [d3247, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3247, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3247, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26641 (p : Pattern) (guard : d5539 p = 1) : d3248 p ≤ (0 : Int) + d2207 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3248, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26634 p hg
    simpa only [d3248, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3248, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26640 p hg
    simpa only [d3248, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26642 (p : Pattern) (guard : d5539 p = 1) : d3249 p ≤ (0 : Int) + d2208 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3249, d2208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26632 p hg
    simpa only [d3249, d2208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3249, d2208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26641 p hg
    simpa only [d3249, d2208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26643 (p : Pattern) (guard : d5268 p = 1) : d3250 p ≤ (0 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3250, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d5268, d3250, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3250, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19972 p hg
    simpa only [d5268, d3250, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26644 (p : Pattern) (guard : d0 p = 1) : d3250 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26645 (p : Pattern) (guard : d5539 p = 1) : d3250 p ≤ (0 : Int) + d2209 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26643 p hg
    simpa only [d5539, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d5539, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26646 (p : Pattern) (guard : d5539 p = 1) : d3251 p ≤ (0 : Int) + d2210 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3251, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26645 p hg
    simpa only [d3251, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3251, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3251, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26647 (p : Pattern) (guard : d5539 p = 1) : d3252 p ≤ (0 : Int) + d2211 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3252, d2211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26610 p hg
    simpa only [d3252, d2211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3252, d2211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26646 p hg
    simpa only [d3252, d2211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26648 (p : Pattern) (guard : d5268 p = 1) : d3253 p ≤ (0 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3253, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14566 p hg
    simpa only [d5268, d3253, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3253, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20051 p hg
    simpa only [d5268, d3253, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26649 (p : Pattern) (guard : d0 p = 1) : d3253 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26650 (p : Pattern) (guard : d5539 p = 1) : d3253 p ≤ (0 : Int) + d2212 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26648 p hg
    simpa only [d5539, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26649 p hg
    simpa only [d5539, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26651 (p : Pattern) (guard : d5539 p = 1) : d3254 p ≤ (0 : Int) + d2213 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3254, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26650 p hg
    simpa only [d3254, d2213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3254, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3254, d2213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26652 (p : Pattern) (guard : d5539 p = 1) : d3255 p ≤ (0 : Int) + d2214 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3255, d2214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26610 p hg
    simpa only [d3255, d2214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3255, d2214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26651 p hg
    simpa only [d3255, d2214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26653 (p : Pattern) (guard : d5539 p = 1) : d3256 p ≤ (0 : Int) + d2215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3256, d2215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26647 p hg
    simpa only [d3256, d2215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3256, d2215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26652 p hg
    simpa only [d3256, d2215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26654 (p : Pattern) (guard : d5268 p = 1) : d3257 p ≤ (0 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3257, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14575 p hg
    simpa only [d5268, d3257, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3257, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20007 p hg
    simpa only [d5268, d3257, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26655 (p : Pattern) (guard : d0 p = 1) : d3257 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26656 (p : Pattern) (guard : d5539 p = 1) : d3257 p ≤ (0 : Int) + d2216 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26654 p hg
    simpa only [d5539, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26655 p hg
    simpa only [d5539, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26657 (p : Pattern) (guard : d5539 p = 1) : d3258 p ≤ (0 : Int) + d2217 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3258, d2217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26656 p hg
    simpa only [d3258, d2217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3258, d2217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3258, d2217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26658 (p : Pattern) (guard : d5539 p = 1) : d3259 p ≤ (0 : Int) + d2218 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3259, d2218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26610 p hg
    simpa only [d3259, d2218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3259, d2218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26657 p hg
    simpa only [d3259, d2218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26659 (p : Pattern) (guard : d5539 p = 1) : d3260 p ≤ (0 : Int) + d2219 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3260, d2219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26628 p hg
    simpa only [d3260, d2219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3260, d2219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3260, d2219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26660 (p : Pattern) (guard : d5539 p = 1) : d3261 p ≤ (0 : Int) + d2220 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3261, d2220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26658 p hg
    simpa only [d3261, d2220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3261, d2220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26659 p hg
    simpa only [d3261, d2220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26661 (p : Pattern) (guard : d5539 p = 1) : d3262 p ≤ (0 : Int) + d2221 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3262, d2221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26653 p hg
    simpa only [d3262, d2221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3262, d2221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26660 p hg
    simpa only [d3262, d2221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26662 (p : Pattern) (guard : d5539 p = 1) : d3263 p ≤ (0 : Int) + d2222 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3263, d2222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26610 p hg
    simpa only [d3263, d2222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3263, d2222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3263, d2222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26663 (p : Pattern) (guard : d5539 p = 1) : d3264 p ≤ (0 : Int) + d2223 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3264, d2223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26662 p hg
    simpa only [d3264, d2223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3264, d2223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26659 p hg
    simpa only [d3264, d2223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26664 (p : Pattern) (guard : d5539 p = 1) : d3265 p ≤ (0 : Int) + d2224 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3265, d2224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26637 p hg
    simpa only [d3265, d2224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3265, d2224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3265, d2224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26665 (p : Pattern) (guard : d5539 p = 1) : d3266 p ≤ (0 : Int) + d2225 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3266, d2225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26664 p hg
    simpa only [d3266, d2225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3266, d2225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3266, d2225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26666 (p : Pattern) (guard : d5539 p = 1) : d3267 p ≤ (0 : Int) + d2226 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3267, d2226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26663 p hg
    simpa only [d3267, d2226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3267, d2226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26665 p hg
    simpa only [d3267, d2226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26667 (p : Pattern) (guard : d5539 p = 1) : d3268 p ≤ (0 : Int) + d2227 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3268, d2227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26661 p hg
    simpa only [d3268, d2227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3268, d2227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26666 p hg
    simpa only [d3268, d2227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26668 (p : Pattern) (guard : d5539 p = 1) : d3269 p ≤ (0 : Int) + d2228 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3269, d2228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26642 p hg
    simpa only [d3269, d2228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3269, d2228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26667 p hg
    simpa only [d3269, d2228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26669 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26670 (p : Pattern) (guard : d5268 p = 1) : d3270 p ≤ (0 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3270, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5268, d3270, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3270, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26669 p hg
    simpa only [d5268, d3270, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26671 (p : Pattern) (guard : d5268 p = 1) : d3271 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26670 p hg
    simpa only [d3271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26672 (p : Pattern) (guard : d0 p = 1) : d3226 p ≤ (0 : Int) + d357 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26673 (p : Pattern) (guard : d5539 p = 1) : d3272 p ≤ (0 : Int) + d2229 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d3272, d2229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26671 p hg
    simpa only [d5539, d3272, d2229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d3272, d2229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26672 p hg
    simpa only [d5539, d3272, d2229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26674 (p : Pattern) (guard : d5539 p = 1) : d3273 p ≤ (0 : Int) + d2230 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3273, d2230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26673 p hg
    simpa only [d3273, d2230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3273, d2230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26610 p hg
    simpa only [d3273, d2230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26675 (p : Pattern) (guard : d5539 p = 1) : d3274 p ≤ (0 : Int) + d2231 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3274, d2231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26674 p hg
    simpa only [d3274, d2231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3274, d2231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26612 p hg
    simpa only [d3274, d2231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26676 (p : Pattern) (guard : d5539 p = 1) : d3275 p ≤ (0 : Int) + d2232 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3275, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26645 p hg
    simpa only [d3275, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3275, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26646 p hg
    simpa only [d3275, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26677 (p : Pattern) (guard : d5539 p = 1) : d3276 p ≤ (0 : Int) + d2233 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3276, d2233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26675 p hg
    simpa only [d3276, d2233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3276, d2233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26676 p hg
    simpa only [d3276, d2233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26678 (p : Pattern) (guard : d5539 p = 1) : d3277 p ≤ (0 : Int) + d2234 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3277, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26630 p hg
    simpa only [d3277, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3277, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26639 p hg
    simpa only [d3277, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26679 (p : Pattern) (guard : d5539 p = 1) : d3278 p ≤ (0 : Int) + d2235 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3278, d2235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26677 p hg
    simpa only [d3278, d2235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3278, d2235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26678 p hg
    simpa only [d3278, d2235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26680 (p : Pattern) (guard : d5268 p = 1) : d3279 p ≤ (0 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3279, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14597 p hg
    simpa only [d5268, d3279, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3279, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19996 p hg
    simpa only [d5268, d3279, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26681 (p : Pattern) (guard : d0 p = 1) : d3279 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26682 (p : Pattern) (guard : d5539 p = 1) : d3279 p ≤ (0 : Int) + d2236 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26680 p hg
    simpa only [d5539, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26681 p hg
    simpa only [d5539, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26683 (p : Pattern) (guard : d5539 p = 1) : d3280 p ≤ (0 : Int) + d2237 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3280, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26682 p hg
    simpa only [d3280, d2237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3280, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3280, d2237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26684 (p : Pattern) (guard : d5539 p = 1) : d3281 p ≤ (0 : Int) + d2238 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3281, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26682 p hg
    simpa only [d3281, d2238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3281, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26683 p hg
    simpa only [d3281, d2238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26685 (p : Pattern) (guard : d5539 p = 1) : d3282 p ≤ (0 : Int) + d2239 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3282, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26630 p hg
    simpa only [d3282, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3282, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26684 p hg
    simpa only [d3282, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26686 (p : Pattern) (guard : d5539 p = 1) : d3283 p ≤ (0 : Int) + d2240 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3283, d2240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26656 p hg
    simpa only [d3283, d2240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3283, d2240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26657 p hg
    simpa only [d3283, d2240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26687 (p : Pattern) (guard : d5539 p = 1) : d3284 p ≤ (0 : Int) + d2241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3284, d2241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26686 p hg
    simpa only [d3284, d2241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3284, d2241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3284, d2241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26688 (p : Pattern) (guard : d5539 p = 1) : d3285 p ≤ (0 : Int) + d2242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3285, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26685 p hg
    simpa only [d3285, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3285, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26687 p hg
    simpa only [d3285, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26689 (p : Pattern) (guard : d5539 p = 1) : d3286 p ≤ (0 : Int) + d2243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3286, d2243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26679 p hg
    simpa only [d3286, d2243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3286, d2243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26688 p hg
    simpa only [d3286, d2243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26690 (p : Pattern) (guard : d5539 p = 1) : d3287 p ≤ (0 : Int) + d2244 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3287, d2244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26645 p hg
    simpa only [d3287, d2244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3287, d2244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3287, d2244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26691 (p : Pattern) (guard : d5539 p = 1) : d3288 p ≤ (0 : Int) + d2245 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3288, d2245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26652 p hg
    simpa only [d3288, d2245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3288, d2245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26690 p hg
    simpa only [d3288, d2245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26692 (p : Pattern) (guard : d5539 p = 1) : d3289 p ≤ (0 : Int) + d2246 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3289, d2246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26659 p hg
    simpa only [d3289, d2246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3289, d2246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26664 p hg
    simpa only [d3289, d2246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26693 (p : Pattern) (guard : d5539 p = 1) : d3290 p ≤ (0 : Int) + d2247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3290, d2247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26691 p hg
    simpa only [d3290, d2247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3290, d2247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26692 p hg
    simpa only [d3290, d2247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26694 (p : Pattern) (guard : d5539 p = 1) : d3291 p ≤ (0 : Int) + d2248 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3291, d2248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26682 p hg
    simpa only [d3291, d2248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3291, d2248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3291, d2248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26695 (p : Pattern) (guard : d5539 p = 1) : d3292 p ≤ (0 : Int) + d2249 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3292, d2249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26659 p hg
    simpa only [d3292, d2249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3292, d2249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26694 p hg
    simpa only [d3292, d2249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26696 (p : Pattern) (guard : d5539 p = 1) : d3293 p ≤ (0 : Int) + d2250 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3293, d2250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26656 p hg
    simpa only [d3293, d2250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3293, d2250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3293, d2250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26697 (p : Pattern) (guard : d5539 p = 1) : d3294 p ≤ (0 : Int) + d2251 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3294, d2251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26696 p hg
    simpa only [d3294, d2251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3294, d2251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3294, d2251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26698 (p : Pattern) (guard : d5539 p = 1) : d3295 p ≤ (0 : Int) + d2252 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3295, d2252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26695 p hg
    simpa only [d3295, d2252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3295, d2252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26697 p hg
    simpa only [d3295, d2252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26699 (p : Pattern) (guard : d5539 p = 1) : d3296 p ≤ (0 : Int) + d2253 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3296, d2253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26693 p hg
    simpa only [d3296, d2253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3296, d2253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26698 p hg
    simpa only [d3296, d2253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26700 (p : Pattern) (guard : d5539 p = 1) : d3297 p ≤ (0 : Int) + d2254 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3297, d2254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26689 p hg
    simpa only [d3297, d2254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3297, d2254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26699 p hg
    simpa only [d3297, d2254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26701 (p : Pattern) (guard : d5539 p = 1) : d3298 p ≤ (0 : Int) + d2255 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3298, d2255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26668 p hg
    simpa only [d3298, d2255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3298, d2255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26700 p hg
    simpa only [d3298, d2255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26702 (p : Pattern) (guard : d5539 p = 1) : d3299 p ≤ (0 : Int) + d2256 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3299, d2256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26633 p hg
    simpa only [d3299, d2256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3299, d2256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26634 p hg
    simpa only [d3299, d2256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26703 (p : Pattern) (guard : d5539 p = 1) : d3300 p ≤ (0 : Int) + d2257 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3300, d2257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26702 p hg
    simpa only [d3300, d2257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3300, d2257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26641 p hg
    simpa only [d3300, d2257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26704 (p : Pattern) (guard : d5539 p = 1) : d3301 p ≤ (0 : Int) + d2258 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3301, d2258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26650 p hg
    simpa only [d3301, d2258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3301, d2258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26651 p hg
    simpa only [d3301, d2258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26705 (p : Pattern) (guard : d5539 p = 1) : d3302 p ≤ (0 : Int) + d2259 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3302, d2259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26676 p hg
    simpa only [d3302, d2259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3302, d2259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26704 p hg
    simpa only [d3302, d2259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26706 (p : Pattern) (guard : d5539 p = 1) : d3303 p ≤ (0 : Int) + d2260 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3303, d2260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26705 p hg
    simpa only [d3303, d2260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3303, d2260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26687 p hg
    simpa only [d3303, d2260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26707 (p : Pattern) (guard : d5539 p = 1) : d3304 p ≤ (0 : Int) + d2261 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3304, d2261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26706 p hg
    simpa only [d3304, d2261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3304, d2261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3304, d2261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26708 (p : Pattern) (guard : d5539 p = 1) : d3305 p ≤ (0 : Int) + d2262 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3305, d2262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26703 p hg
    simpa only [d3305, d2262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3305, d2262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26707 p hg
    simpa only [d3305, d2262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26709 (p : Pattern) (guard : d5539 p = 1) : d3306 p ≤ (0 : Int) + d2263 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3306, d2263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26633 p hg
    simpa only [d3306, d2263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3306, d2263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26676 p hg
    simpa only [d3306, d2263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26710 (p : Pattern) (guard : d5539 p = 1) : d3307 p ≤ (0 : Int) + d2264 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3307, d2264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26709 p hg
    simpa only [d3307, d2264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3307, d2264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26678 p hg
    simpa only [d3307, d2264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26711 (p : Pattern) (guard : d5539 p = 1) : d3308 p ≤ (0 : Int) + d2265 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3308, d2265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26710 p hg
    simpa only [d3308, d2265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3308, d2265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26688 p hg
    simpa only [d3308, d2265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26712 (p : Pattern) (guard : d5539 p = 1) : d3309 p ≤ (0 : Int) + d2266 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3309, d2266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26704 p hg
    simpa only [d3309, d2266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3309, d2266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3309, d2266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26713 (p : Pattern) (guard : d5539 p = 1) : d3310 p ≤ (0 : Int) + d2267 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3310, d2267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26712 p hg
    simpa only [d3310, d2267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3310, d2267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3310, d2267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26714 (p : Pattern) (guard : d5539 p = 1) : d3311 p ≤ (0 : Int) + d2268 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3311, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26713 p hg
    simpa only [d3311, d2268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3311, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3311, d2268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26715 (p : Pattern) (guard : d5539 p = 1) : d3312 p ≤ (0 : Int) + d2269 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3312, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26711 p hg
    simpa only [d3312, d2269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3312, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26714 p hg
    simpa only [d3312, d2269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26716 (p : Pattern) (guard : d5539 p = 1) : d3313 p ≤ (0 : Int) + d2270 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3313, d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26708 p hg
    simpa only [d3313, d2270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3313, d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26715 p hg
    simpa only [d3313, d2270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26717 (p : Pattern) (guard : d5539 p = 1) : d3314 p ≤ (0 : Int) + d2271 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3314, d2271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26701 p hg
    simpa only [d3314, d2271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3314, d2271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26716 p hg
    simpa only [d3314, d2271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26718 (p : Pattern) (guard : d5539 p = 1) : d3238 p ≤ (0 : Int) + d2272 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26625 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26633 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26719 (p : Pattern) (guard : d5539 p = 1) : d3299 p ≤ (0 : Int) + d2273 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3299, d2273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26718 p hg
    simpa only [d3299, d2273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3299, d2273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26634 p hg
    simpa only [d3299, d2273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26720 (p : Pattern) (guard : d5539 p = 1) : d3300 p ≤ (0 : Int) + d2274 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3300, d2274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26719 p hg
    simpa only [d3300, d2274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3300, d2274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26641 p hg
    simpa only [d3300, d2274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26721 (p : Pattern) (guard : d5539 p = 1) : d3305 p ≤ (0 : Int) + d2275 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3305, d2275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26720 p hg
    simpa only [d3305, d2275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3305, d2275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26707 p hg
    simpa only [d3305, d2275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26722 (p : Pattern) (guard : d5539 p = 1) : d3313 p ≤ (0 : Int) + d2276 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3313, d2276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26721 p hg
    simpa only [d3313, d2276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3313, d2276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26715 p hg
    simpa only [d3313, d2276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26723 (p : Pattern) (guard : d5539 p = 1) : d3315 p ≤ (0 : Int) + d2277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3315, d2277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26639 p hg
    simpa only [d3315, d2277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3315, d2277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26686 p hg
    simpa only [d3315, d2277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26724 (p : Pattern) (guard : d5539 p = 1) : d3316 p ≤ (0 : Int) + d2278 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3316, d2278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26723 p hg
    simpa only [d3316, d2278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3316, d2278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26687 p hg
    simpa only [d3316, d2278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26725 (p : Pattern) (guard : d5539 p = 1) : d3317 p ≤ (0 : Int) + d2279 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3317, d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26687 p hg
    simpa only [d3317, d2279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3317, d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3317, d2279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26726 (p : Pattern) (guard : d5539 p = 1) : d3318 p ≤ (0 : Int) + d2280 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3318, d2280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26724 p hg
    simpa only [d3318, d2280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3318, d2280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26725 p hg
    simpa only [d3318, d2280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26727 (p : Pattern) (guard : d5539 p = 1) : d3319 p ≤ (0 : Int) + d2281 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3319, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26725 p hg
    simpa only [d3319, d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3319, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3319, d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26728 (p : Pattern) (guard : d5539 p = 1) : d3320 p ≤ (0 : Int) + d2282 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3320, d2282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26726 p hg
    simpa only [d3320, d2282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3320, d2282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26727 p hg
    simpa only [d3320, d2282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26729 (p : Pattern) (guard : d5539 p = 1) : d3321 p ≤ (0 : Int) + d2283 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3321, d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26727 p hg
    simpa only [d3321, d2283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3321, d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3321, d2283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26730 (p : Pattern) (guard : d5539 p = 1) : d3322 p ≤ (0 : Int) + d2284 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3322, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26728 p hg
    simpa only [d3322, d2284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3322, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26729 p hg
    simpa only [d3322, d2284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26731 (p : Pattern) (guard : d5539 p = 1) : d3323 p ≤ (0 : Int) + d2285 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3323, d2285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26722 p hg
    simpa only [d3323, d2285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3323, d2285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26730 p hg
    simpa only [d3323, d2285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26732 (p : Pattern) (guard : d5539 p = 1) : d3324 p ≤ (0 : Int) + d2286 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3324, d2286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26717 p hg
    simpa only [d3324, d2286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3324, d2286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26731 p hg
    simpa only [d3324, d2286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26733 (p : Pattern) (guard : d5539 p = 1) : d3325 p ≤ (0 : Int) + d2287 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3325, d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26620 p hg
    simpa only [d3325, d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3325, d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26633 p hg
    simpa only [d3325, d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26734 (p : Pattern) (guard : d5539 p = 1) : d3326 p ≤ (0 : Int) + d2288 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3326, d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26733 p hg
    simpa only [d3326, d2288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3326, d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26634 p hg
    simpa only [d3326, d2288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26735 (p : Pattern) (guard : d5539 p = 1) : d3327 p ≤ (0 : Int) + d2289 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3327, d2289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26734 p hg
    simpa only [d3327, d2289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3327, d2289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26641 p hg
    simpa only [d3327, d2289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26736 (p : Pattern) (guard : d5539 p = 1) : d3328 p ≤ (0 : Int) + d2290 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3328, d2290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26735 p hg
    simpa only [d3328, d2290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3328, d2290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26667 p hg
    simpa only [d3328, d2290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26737 (p : Pattern) (guard : d5539 p = 1) : d3329 p ≤ (0 : Int) + d2291 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3329, d2291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26711 p hg
    simpa only [d3329, d2291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3329, d2291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26699 p hg
    simpa only [d3329, d2291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26738 (p : Pattern) (guard : d5539 p = 1) : d3330 p ≤ (0 : Int) + d2292 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3330, d2292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26736 p hg
    simpa only [d3330, d2292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3330, d2292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26737 p hg
    simpa only [d3330, d2292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26739 (p : Pattern) (guard : d5539 p = 1) : d3331 p ≤ (0 : Int) + d2293 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3331, d2293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26738 p hg
    simpa only [d3331, d2293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3331, d2293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26716 p hg
    simpa only [d3331, d2293, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
