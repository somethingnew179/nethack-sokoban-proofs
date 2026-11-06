/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons132
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare18620 (p : Pattern) (guard : d4902 p = 1) : d2492 p ≤ (2 : Int) + d257 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2492, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18500 p hg
    simpa only [d2492, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2492, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18364 p hg
    simpa only [d2492, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18621 (p : Pattern) (guard : d4902 p = 1) : d2493 p ≤ (2 : Int) + d258 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2493, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18620 p hg
    simpa only [d2493, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2493, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2493, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18622 (p : Pattern) (guard : d4902 p = 1) : d2494 p ≤ (2 : Int) + d259 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2494, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18621 p hg
    simpa only [d2494, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2494, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2494, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18623 (p : Pattern) (guard : d4902 p = 1) : d2495 p ≤ (2 : Int) + d260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2495, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18619 p hg
    simpa only [d2495, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2495, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18622 p hg
    simpa only [d2495, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18624 (p : Pattern) (guard : d4902 p = 1) : d2496 p ≤ (2 : Int) + d261 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2496, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18623 p hg
    simpa only [d2496, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2496, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18612 p hg
    simpa only [d2496, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18625 (p : Pattern) (guard : d4902 p = 1) : d2497 p ≤ (2 : Int) + d262 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2497, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18624 p hg
    simpa only [d2497, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2497, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2497, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18626 (p : Pattern) (guard : d4902 p = 1) : d2498 p ≤ (2 : Int) + d263 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2498, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18614 p hg
    simpa only [d2498, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2498, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18625 p hg
    simpa only [d2498, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18627 (p : Pattern) (guard : d4902 p = 1) : d2499 p ≤ (2 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2499, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18588 p hg
    simpa only [d2499, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2499, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18626 p hg
    simpa only [d2499, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18628 (p : Pattern) (guard : d4902 p = 1) : d2500 p ≤ (2 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2500, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18420 p hg
    simpa only [d2500, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2500, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18627 p hg
    simpa only [d2500, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18629 (p : Pattern) (guard : d4902 p = 1) : d2501 p ≤ (2 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2501, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18571 p hg
    simpa only [d2501, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2501, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18628 p hg
    simpa only [d2501, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18630 (p : Pattern) (guard : d4902 p = 1) : d2502 p ≤ (2 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2502, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18531 p hg
    simpa only [d2502, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2502, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18629 p hg
    simpa only [d2502, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18631 (p : Pattern) (guard : d0 p = 1) : d318 p ≤ (0 : Int) + d3226 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18632 (p : Pattern) (guard : d5539 p = 1) : d2184 p ≤ (0 : Int) + d3228 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2184, d3228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17646 p hg
    simpa only [d5539, d2184, d3228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2184, d3228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18631 p hg
    simpa only [d5539, d2184, d3228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18633 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3226 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18634 (p : Pattern) (guard : d5539 p = 1) : d2185 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d5539, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18633 p hg
    simpa only [d5539, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18635 (p : Pattern) (guard : d5539 p = 1) : d2186 p ≤ (0 : Int) + d3229 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2186, d3229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18632 p hg
    simpa only [d2186, d3229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2186, d3229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18634 p hg
    simpa only [d2186, d3229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18636 (p : Pattern) (guard : d5539 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare18637 (p : Pattern) (guard : d5539 p = 1) : d2187 p ≤ (0 : Int) + d3230 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2187, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18634 p hg
    simpa only [d2187, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2187, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2187, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18638 (p : Pattern) (guard : d5539 p = 1) : d2188 p ≤ (0 : Int) + d3231 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2188, d3231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18635 p hg
    simpa only [d2188, d3231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2188, d3231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18637 p hg
    simpa only [d2188, d3231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18639 (p : Pattern) (guard : d0 p = 1) : d330 p ≤ (0 : Int) + d3226 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18640 (p : Pattern) (guard : d5539 p = 1) : d2189 p ≤ (0 : Int) + d3234 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2189, d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17654 p hg
    simpa only [d5539, d2189, d3234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2189, d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18639 p hg
    simpa only [d5539, d2189, d3234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18641 (p : Pattern) (guard : d5539 p = 1) : d2190 p ≤ (0 : Int) + d3235 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2190, d3235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18640 p hg
    simpa only [d2190, d3235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2190, d3235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18634 p hg
    simpa only [d2190, d3235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18642 (p : Pattern) (guard : d5539 p = 1) : d2191 p ≤ (0 : Int) + d3236 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2191, d3236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18641 p hg
    simpa only [d2191, d3236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2191, d3236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18637 p hg
    simpa only [d2191, d3236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18643 (p : Pattern) (guard : d5539 p = 1) : d2192 p ≤ (0 : Int) + d3237 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2192, d3237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18638 p hg
    simpa only [d2192, d3237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2192, d3237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18642 p hg
    simpa only [d2192, d3237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18644 (p : Pattern) (guard : d0 p = 1) : d332 p ≤ (0 : Int) + d3226 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18645 (p : Pattern) (guard : d5539 p = 1) : d2193 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d5539, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18644 p hg
    simpa only [d5539, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18646 (p : Pattern) (guard : d5539 p = 1) : d2194 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18645 p hg
    simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18634 p hg
    simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18647 (p : Pattern) (guard : d5539 p = 1) : d2195 p ≤ (0 : Int) + d3238 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2195, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18646 p hg
    simpa only [d2195, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2195, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18637 p hg
    simpa only [d2195, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18648 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3239 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18649 (p : Pattern) (guard : d5539 p = 1) : d2196 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17661 p hg
    simpa only [d5539, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18648 p hg
    simpa only [d5539, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18650 (p : Pattern) (guard : d5539 p = 1) : d2197 p ≤ (0 : Int) + d3240 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2197, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18649 p hg
    simpa only [d2197, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2197, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2197, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18651 (p : Pattern) (guard : d5539 p = 1) : d2198 p ≤ (0 : Int) + d3241 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2198, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18649 p hg
    simpa only [d2198, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2198, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18650 p hg
    simpa only [d2198, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18652 (p : Pattern) (guard : d5539 p = 1) : d2199 p ≤ (0 : Int) + d3242 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2199, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18647 p hg
    simpa only [d2199, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2199, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18651 p hg
    simpa only [d2199, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18653 (p : Pattern) (guard : d5539 p = 1) : d2200 p ≤ (0 : Int) + d3243 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2200, d3243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18643 p hg
    simpa only [d2200, d3243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2200, d3243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18652 p hg
    simpa only [d2200, d3243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18654 (p : Pattern) (guard : d5539 p = 1) : d2201 p ≤ (0 : Int) + d3238 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2201, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18634 p hg
    simpa only [d2201, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2201, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18637 p hg
    simpa only [d2201, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18655 (p : Pattern) (guard : d5539 p = 1) : d2202 p ≤ (0 : Int) + d3242 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2202, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18654 p hg
    simpa only [d2202, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2202, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18651 p hg
    simpa only [d2202, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18656 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3244 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18657 (p : Pattern) (guard : d5539 p = 1) : d2203 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17667 p hg
    simpa only [d5539, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18656 p hg
    simpa only [d5539, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18658 (p : Pattern) (guard : d5539 p = 1) : d2204 p ≤ (0 : Int) + d3245 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2204, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18657 p hg
    simpa only [d2204, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2204, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2204, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18659 (p : Pattern) (guard : d5539 p = 1) : d2205 p ≤ (0 : Int) + d3246 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2205, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18657 p hg
    simpa only [d2205, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2205, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18658 p hg
    simpa only [d2205, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18660 (p : Pattern) (guard : d5539 p = 1) : d2206 p ≤ (0 : Int) + d3247 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2206, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18659 p hg
    simpa only [d2206, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2206, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2206, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18661 (p : Pattern) (guard : d5539 p = 1) : d2207 p ≤ (0 : Int) + d3248 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2207, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18655 p hg
    simpa only [d2207, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2207, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18660 p hg
    simpa only [d2207, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18662 (p : Pattern) (guard : d5539 p = 1) : d2208 p ≤ (0 : Int) + d3249 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2208, d3249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18653 p hg
    simpa only [d2208, d3249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2208, d3249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18661 p hg
    simpa only [d2208, d3249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18663 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3250 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18664 (p : Pattern) (guard : d5539 p = 1) : d2209 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17674 p hg
    simpa only [d5539, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18663 p hg
    simpa only [d5539, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18665 (p : Pattern) (guard : d5539 p = 1) : d2210 p ≤ (0 : Int) + d3251 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2210, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18664 p hg
    simpa only [d2210, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2210, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2210, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18666 (p : Pattern) (guard : d5539 p = 1) : d2211 p ≤ (0 : Int) + d3252 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2211, d3252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18634 p hg
    simpa only [d2211, d3252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2211, d3252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18665 p hg
    simpa only [d2211, d3252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18667 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3253 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18668 (p : Pattern) (guard : d5539 p = 1) : d2212 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17678 p hg
    simpa only [d5539, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18667 p hg
    simpa only [d5539, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18669 (p : Pattern) (guard : d5539 p = 1) : d2213 p ≤ (0 : Int) + d3254 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2213, d3254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18668 p hg
    simpa only [d2213, d3254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2213, d3254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2213, d3254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18670 (p : Pattern) (guard : d5539 p = 1) : d2214 p ≤ (0 : Int) + d3255 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2214, d3255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18634 p hg
    simpa only [d2214, d3255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2214, d3255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18669 p hg
    simpa only [d2214, d3255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18671 (p : Pattern) (guard : d5539 p = 1) : d2215 p ≤ (0 : Int) + d3256 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2215, d3256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18666 p hg
    simpa only [d2215, d3256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2215, d3256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18670 p hg
    simpa only [d2215, d3256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18672 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3257 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18673 (p : Pattern) (guard : d5539 p = 1) : d2216 p ≤ (0 : Int) + d3257 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17683 p hg
    simpa only [d5539, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18672 p hg
    simpa only [d5539, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18674 (p : Pattern) (guard : d5539 p = 1) : d2217 p ≤ (0 : Int) + d3258 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2217, d3258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18673 p hg
    simpa only [d2217, d3258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2217, d3258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2217, d3258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18675 (p : Pattern) (guard : d5539 p = 1) : d2218 p ≤ (0 : Int) + d3259 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2218, d3259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18634 p hg
    simpa only [d2218, d3259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2218, d3259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18674 p hg
    simpa only [d2218, d3259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18676 (p : Pattern) (guard : d5539 p = 1) : d2219 p ≤ (0 : Int) + d3260 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2219, d3260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18649 p hg
    simpa only [d2219, d3260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2219, d3260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2219, d3260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18677 (p : Pattern) (guard : d5539 p = 1) : d2220 p ≤ (0 : Int) + d3261 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2220, d3261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18675 p hg
    simpa only [d2220, d3261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2220, d3261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18676 p hg
    simpa only [d2220, d3261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18678 (p : Pattern) (guard : d5539 p = 1) : d2221 p ≤ (0 : Int) + d3262 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2221, d3262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18671 p hg
    simpa only [d2221, d3262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2221, d3262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18677 p hg
    simpa only [d2221, d3262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18679 (p : Pattern) (guard : d5539 p = 1) : d2222 p ≤ (0 : Int) + d3263 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2222, d3263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18634 p hg
    simpa only [d2222, d3263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2222, d3263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2222, d3263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18680 (p : Pattern) (guard : d5539 p = 1) : d2223 p ≤ (0 : Int) + d3264 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2223, d3264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18679 p hg
    simpa only [d2223, d3264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2223, d3264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18676 p hg
    simpa only [d2223, d3264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18681 (p : Pattern) (guard : d5539 p = 1) : d2224 p ≤ (0 : Int) + d3265 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2224, d3265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18657 p hg
    simpa only [d2224, d3265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2224, d3265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2224, d3265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18682 (p : Pattern) (guard : d5539 p = 1) : d2225 p ≤ (0 : Int) + d3266 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2225, d3266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18681 p hg
    simpa only [d2225, d3266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2225, d3266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2225, d3266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18683 (p : Pattern) (guard : d5539 p = 1) : d2226 p ≤ (0 : Int) + d3267 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2226, d3267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18680 p hg
    simpa only [d2226, d3267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2226, d3267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18682 p hg
    simpa only [d2226, d3267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18684 (p : Pattern) (guard : d5539 p = 1) : d2227 p ≤ (0 : Int) + d3268 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2227, d3268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18678 p hg
    simpa only [d2227, d3268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2227, d3268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18683 p hg
    simpa only [d2227, d3268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18685 (p : Pattern) (guard : d5539 p = 1) : d2228 p ≤ (0 : Int) + d3269 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2228, d3269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18662 p hg
    simpa only [d2228, d3269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2228, d3269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18684 p hg
    simpa only [d2228, d3269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18686 (p : Pattern) (guard : d0 p = 1) : d357 p ≤ (0 : Int) + d3226 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18687 (p : Pattern) (guard : d5539 p = 1) : d2229 p ≤ (0 : Int) + d3272 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2229, d3272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17698 p hg
    simpa only [d5539, d2229, d3272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2229, d3272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18686 p hg
    simpa only [d5539, d2229, d3272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18688 (p : Pattern) (guard : d5539 p = 1) : d2230 p ≤ (0 : Int) + d3273 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2230, d3273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18687 p hg
    simpa only [d2230, d3273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2230, d3273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18634 p hg
    simpa only [d2230, d3273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18689 (p : Pattern) (guard : d5539 p = 1) : d2231 p ≤ (0 : Int) + d3274 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2231, d3274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18688 p hg
    simpa only [d2231, d3274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2231, d3274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18637 p hg
    simpa only [d2231, d3274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18690 (p : Pattern) (guard : d5539 p = 1) : d2232 p ≤ (0 : Int) + d3275 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2232, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18664 p hg
    simpa only [d2232, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2232, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18665 p hg
    simpa only [d2232, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18691 (p : Pattern) (guard : d5539 p = 1) : d2233 p ≤ (0 : Int) + d3276 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2233, d3276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18689 p hg
    simpa only [d2233, d3276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2233, d3276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18690 p hg
    simpa only [d2233, d3276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18692 (p : Pattern) (guard : d5539 p = 1) : d2234 p ≤ (0 : Int) + d3277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2234, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18651 p hg
    simpa only [d2234, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2234, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18659 p hg
    simpa only [d2234, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18693 (p : Pattern) (guard : d5539 p = 1) : d2235 p ≤ (0 : Int) + d3278 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2235, d3278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18691 p hg
    simpa only [d2235, d3278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2235, d3278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18692 p hg
    simpa only [d2235, d3278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18694 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3279 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18695 (p : Pattern) (guard : d5539 p = 1) : d2236 p ≤ (0 : Int) + d3279 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17707 p hg
    simpa only [d5539, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18694 p hg
    simpa only [d5539, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18696 (p : Pattern) (guard : d5539 p = 1) : d2237 p ≤ (0 : Int) + d3280 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2237, d3280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18695 p hg
    simpa only [d2237, d3280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2237, d3280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2237, d3280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18697 (p : Pattern) (guard : d5539 p = 1) : d2238 p ≤ (0 : Int) + d3281 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2238, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18695 p hg
    simpa only [d2238, d3281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2238, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18696 p hg
    simpa only [d2238, d3281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18698 (p : Pattern) (guard : d5539 p = 1) : d2239 p ≤ (0 : Int) + d3282 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2239, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18651 p hg
    simpa only [d2239, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2239, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18697 p hg
    simpa only [d2239, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18699 (p : Pattern) (guard : d5539 p = 1) : d2240 p ≤ (0 : Int) + d3283 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2240, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18673 p hg
    simpa only [d2240, d3283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2240, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18674 p hg
    simpa only [d2240, d3283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18700 (p : Pattern) (guard : d5539 p = 1) : d2241 p ≤ (0 : Int) + d3284 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2241, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18699 p hg
    simpa only [d2241, d3284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2241, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2241, d3284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18701 (p : Pattern) (guard : d5539 p = 1) : d2242 p ≤ (0 : Int) + d3285 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2242, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18698 p hg
    simpa only [d2242, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2242, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18700 p hg
    simpa only [d2242, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18702 (p : Pattern) (guard : d5539 p = 1) : d2243 p ≤ (0 : Int) + d3286 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2243, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18693 p hg
    simpa only [d2243, d3286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2243, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18701 p hg
    simpa only [d2243, d3286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18703 (p : Pattern) (guard : d5539 p = 1) : d2244 p ≤ (0 : Int) + d3287 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2244, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18664 p hg
    simpa only [d2244, d3287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2244, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2244, d3287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18704 (p : Pattern) (guard : d5539 p = 1) : d2245 p ≤ (0 : Int) + d3288 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2245, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18670 p hg
    simpa only [d2245, d3288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2245, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18703 p hg
    simpa only [d2245, d3288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18705 (p : Pattern) (guard : d5539 p = 1) : d2246 p ≤ (0 : Int) + d3289 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2246, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18676 p hg
    simpa only [d2246, d3289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2246, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18681 p hg
    simpa only [d2246, d3289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18706 (p : Pattern) (guard : d5539 p = 1) : d2247 p ≤ (0 : Int) + d3290 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2247, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18704 p hg
    simpa only [d2247, d3290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2247, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18705 p hg
    simpa only [d2247, d3290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18707 (p : Pattern) (guard : d5539 p = 1) : d2248 p ≤ (0 : Int) + d3291 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2248, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18695 p hg
    simpa only [d2248, d3291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2248, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2248, d3291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18708 (p : Pattern) (guard : d5539 p = 1) : d2249 p ≤ (0 : Int) + d3292 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2249, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18676 p hg
    simpa only [d2249, d3292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2249, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18707 p hg
    simpa only [d2249, d3292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18709 (p : Pattern) (guard : d5539 p = 1) : d2250 p ≤ (0 : Int) + d3293 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2250, d3293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18673 p hg
    simpa only [d2250, d3293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2250, d3293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2250, d3293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18710 (p : Pattern) (guard : d5539 p = 1) : d2251 p ≤ (0 : Int) + d3294 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2251, d3294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18709 p hg
    simpa only [d2251, d3294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2251, d3294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2251, d3294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18711 (p : Pattern) (guard : d5539 p = 1) : d2252 p ≤ (0 : Int) + d3295 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2252, d3295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18708 p hg
    simpa only [d2252, d3295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2252, d3295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18710 p hg
    simpa only [d2252, d3295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18712 (p : Pattern) (guard : d5539 p = 1) : d2253 p ≤ (0 : Int) + d3296 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2253, d3296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18706 p hg
    simpa only [d2253, d3296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2253, d3296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18711 p hg
    simpa only [d2253, d3296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18713 (p : Pattern) (guard : d5539 p = 1) : d2254 p ≤ (0 : Int) + d3297 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2254, d3297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18702 p hg
    simpa only [d2254, d3297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2254, d3297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18712 p hg
    simpa only [d2254, d3297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18714 (p : Pattern) (guard : d5539 p = 1) : d2255 p ≤ (0 : Int) + d3298 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2255, d3298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18685 p hg
    simpa only [d2255, d3298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2255, d3298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18713 p hg
    simpa only [d2255, d3298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18715 (p : Pattern) (guard : d5539 p = 1) : d2256 p ≤ (0 : Int) + d3299 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2256, d3299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18654 p hg
    simpa only [d2256, d3299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2256, d3299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18655 p hg
    simpa only [d2256, d3299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18716 (p : Pattern) (guard : d5539 p = 1) : d2257 p ≤ (0 : Int) + d3300 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2257, d3300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18715 p hg
    simpa only [d2257, d3300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2257, d3300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18661 p hg
    simpa only [d2257, d3300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18717 (p : Pattern) (guard : d5539 p = 1) : d2258 p ≤ (0 : Int) + d3301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2258, d3301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18668 p hg
    simpa only [d2258, d3301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2258, d3301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18669 p hg
    simpa only [d2258, d3301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18718 (p : Pattern) (guard : d5539 p = 1) : d2259 p ≤ (0 : Int) + d3302 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2259, d3302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18690 p hg
    simpa only [d2259, d3302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2259, d3302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18717 p hg
    simpa only [d2259, d3302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18719 (p : Pattern) (guard : d5539 p = 1) : d2260 p ≤ (0 : Int) + d3303 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2260, d3303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18718 p hg
    simpa only [d2260, d3303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2260, d3303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18700 p hg
    simpa only [d2260, d3303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18720 (p : Pattern) (guard : d5539 p = 1) : d2261 p ≤ (0 : Int) + d3304 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2261, d3304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18719 p hg
    simpa only [d2261, d3304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2261, d3304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2261, d3304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18721 (p : Pattern) (guard : d5539 p = 1) : d2262 p ≤ (0 : Int) + d3305 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2262, d3305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18716 p hg
    simpa only [d2262, d3305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2262, d3305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18720 p hg
    simpa only [d2262, d3305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18722 (p : Pattern) (guard : d5539 p = 1) : d2263 p ≤ (0 : Int) + d3306 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2263, d3306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18654 p hg
    simpa only [d2263, d3306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2263, d3306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18690 p hg
    simpa only [d2263, d3306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18723 (p : Pattern) (guard : d5539 p = 1) : d2264 p ≤ (0 : Int) + d3307 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2264, d3307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18722 p hg
    simpa only [d2264, d3307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2264, d3307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18692 p hg
    simpa only [d2264, d3307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18724 (p : Pattern) (guard : d5539 p = 1) : d2265 p ≤ (0 : Int) + d3308 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2265, d3308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18723 p hg
    simpa only [d2265, d3308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2265, d3308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18701 p hg
    simpa only [d2265, d3308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18725 (p : Pattern) (guard : d5539 p = 1) : d2266 p ≤ (0 : Int) + d3309 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2266, d3309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18717 p hg
    simpa only [d2266, d3309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2266, d3309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2266, d3309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18726 (p : Pattern) (guard : d5539 p = 1) : d2267 p ≤ (0 : Int) + d3310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2267, d3310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18725 p hg
    simpa only [d2267, d3310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2267, d3310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2267, d3310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18727 (p : Pattern) (guard : d5539 p = 1) : d2268 p ≤ (0 : Int) + d3311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2268, d3311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18726 p hg
    simpa only [d2268, d3311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2268, d3311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2268, d3311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18728 (p : Pattern) (guard : d5539 p = 1) : d2269 p ≤ (0 : Int) + d3312 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2269, d3312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18724 p hg
    simpa only [d2269, d3312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2269, d3312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18727 p hg
    simpa only [d2269, d3312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18729 (p : Pattern) (guard : d5539 p = 1) : d2270 p ≤ (0 : Int) + d3313 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2270, d3313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18721 p hg
    simpa only [d2270, d3313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2270, d3313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18728 p hg
    simpa only [d2270, d3313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18730 (p : Pattern) (guard : d5539 p = 1) : d2271 p ≤ (0 : Int) + d3314 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2271, d3314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18714 p hg
    simpa only [d2271, d3314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2271, d3314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18729 p hg
    simpa only [d2271, d3314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18731 (p : Pattern) (guard : d5539 p = 1) : d2272 p ≤ (0 : Int) + d3238 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18647 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18654 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18732 (p : Pattern) (guard : d5539 p = 1) : d2273 p ≤ (0 : Int) + d3299 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2273, d3299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18731 p hg
    simpa only [d2273, d3299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2273, d3299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18655 p hg
    simpa only [d2273, d3299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18733 (p : Pattern) (guard : d5539 p = 1) : d2274 p ≤ (0 : Int) + d3300 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2274, d3300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18732 p hg
    simpa only [d2274, d3300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2274, d3300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18661 p hg
    simpa only [d2274, d3300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18734 (p : Pattern) (guard : d5539 p = 1) : d2275 p ≤ (0 : Int) + d3305 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2275, d3305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18733 p hg
    simpa only [d2275, d3305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2275, d3305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18720 p hg
    simpa only [d2275, d3305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18735 (p : Pattern) (guard : d5539 p = 1) : d2276 p ≤ (0 : Int) + d3313 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2276, d3313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18734 p hg
    simpa only [d2276, d3313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2276, d3313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18728 p hg
    simpa only [d2276, d3313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18736 (p : Pattern) (guard : d5539 p = 1) : d2277 p ≤ (0 : Int) + d3315 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2277, d3315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18659 p hg
    simpa only [d2277, d3315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2277, d3315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18699 p hg
    simpa only [d2277, d3315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18737 (p : Pattern) (guard : d5539 p = 1) : d2278 p ≤ (0 : Int) + d3316 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2278, d3316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18736 p hg
    simpa only [d2278, d3316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2278, d3316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18700 p hg
    simpa only [d2278, d3316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18738 (p : Pattern) (guard : d5539 p = 1) : d2279 p ≤ (0 : Int) + d3317 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2279, d3317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18700 p hg
    simpa only [d2279, d3317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2279, d3317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2279, d3317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18739 (p : Pattern) (guard : d5539 p = 1) : d2280 p ≤ (0 : Int) + d3318 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2280, d3318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18737 p hg
    simpa only [d2280, d3318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2280, d3318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18738 p hg
    simpa only [d2280, d3318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18740 (p : Pattern) (guard : d5539 p = 1) : d2281 p ≤ (0 : Int) + d3319 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2281, d3319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18738 p hg
    simpa only [d2281, d3319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2281, d3319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2281, d3319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18741 (p : Pattern) (guard : d5539 p = 1) : d2282 p ≤ (0 : Int) + d3320 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2282, d3320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18739 p hg
    simpa only [d2282, d3320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2282, d3320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18740 p hg
    simpa only [d2282, d3320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18742 (p : Pattern) (guard : d5539 p = 1) : d2283 p ≤ (0 : Int) + d3321 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2283, d3321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18740 p hg
    simpa only [d2283, d3321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2283, d3321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2283, d3321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18743 (p : Pattern) (guard : d5539 p = 1) : d2284 p ≤ (0 : Int) + d3322 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2284, d3322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18741 p hg
    simpa only [d2284, d3322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2284, d3322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18742 p hg
    simpa only [d2284, d3322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18744 (p : Pattern) (guard : d5539 p = 1) : d2285 p ≤ (0 : Int) + d3323 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2285, d3323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18735 p hg
    simpa only [d2285, d3323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2285, d3323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18743 p hg
    simpa only [d2285, d3323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18745 (p : Pattern) (guard : d5539 p = 1) : d2286 p ≤ (0 : Int) + d3324 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2286, d3324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18730 p hg
    simpa only [d2286, d3324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2286, d3324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18744 p hg
    simpa only [d2286, d3324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18746 (p : Pattern) (guard : d5539 p = 1) : d2287 p ≤ (0 : Int) + d3325 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2287, d3325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18642 p hg
    simpa only [d2287, d3325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2287, d3325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18654 p hg
    simpa only [d2287, d3325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18747 (p : Pattern) (guard : d5539 p = 1) : d2288 p ≤ (0 : Int) + d3326 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2288, d3326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18746 p hg
    simpa only [d2288, d3326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2288, d3326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18655 p hg
    simpa only [d2288, d3326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18748 (p : Pattern) (guard : d5539 p = 1) : d2289 p ≤ (0 : Int) + d3327 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2289, d3327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18747 p hg
    simpa only [d2289, d3327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2289, d3327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18661 p hg
    simpa only [d2289, d3327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18749 (p : Pattern) (guard : d5539 p = 1) : d2290 p ≤ (0 : Int) + d3328 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2290, d3328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18748 p hg
    simpa only [d2290, d3328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2290, d3328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18684 p hg
    simpa only [d2290, d3328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18750 (p : Pattern) (guard : d5539 p = 1) : d2291 p ≤ (0 : Int) + d3329 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2291, d3329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18724 p hg
    simpa only [d2291, d3329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2291, d3329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18712 p hg
    simpa only [d2291, d3329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18751 (p : Pattern) (guard : d5539 p = 1) : d2292 p ≤ (0 : Int) + d3330 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2292, d3330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18749 p hg
    simpa only [d2292, d3330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2292, d3330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18750 p hg
    simpa only [d2292, d3330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18752 (p : Pattern) (guard : d5539 p = 1) : d2293 p ≤ (0 : Int) + d3331 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2293, d3331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18751 p hg
    simpa only [d2293, d3331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2293, d3331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18729 p hg
    simpa only [d2293, d3331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18753 (p : Pattern) (guard : d5539 p = 1) : d2294 p ≤ (0 : Int) + d3332 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2294, d3332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18729 p hg
    simpa only [d2294, d3332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2294, d3332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2294, d3332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18754 (p : Pattern) (guard : d5539 p = 1) : d2295 p ≤ (0 : Int) + d3333 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2295, d3333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18752 p hg
    simpa only [d2295, d3333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2295, d3333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18753 p hg
    simpa only [d2295, d3333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18755 (p : Pattern) (guard : d5539 p = 1) : d2296 p ≤ (0 : Int) + d3334 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2296, d3334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18745 p hg
    simpa only [d2296, d3334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2296, d3334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18754 p hg
    simpa only [d2296, d3334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18756 (p : Pattern) (guard : d0 p = 1) : d320 p ≤ (0 : Int) + d3226 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18757 (p : Pattern) (guard : d5539 p = 1) : d2297 p ≤ (0 : Int) + d3337 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2297, d3337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17765 p hg
    simpa only [d5539, d2297, d3337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2297, d3337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18756 p hg
    simpa only [d5539, d2297, d3337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18758 (p : Pattern) (guard : d5539 p = 1) : d2298 p ≤ (0 : Int) + d3338 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2298, d3338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18757 p hg
    simpa only [d2298, d3338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2298, d3338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18634 p hg
    simpa only [d2298, d3338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18759 (p : Pattern) (guard : d5539 p = 1) : d2299 p ≤ (0 : Int) + d3339 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2299, d3339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18758 p hg
    simpa only [d2299, d3339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2299, d3339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18637 p hg
    simpa only [d2299, d3339, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
