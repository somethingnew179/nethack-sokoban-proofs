/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons133
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare18760 (p : Pattern) (guard : d5539 p = 1) : d2300 p ≤ (0 : Int) + d3340 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2300, d3340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18759 p hg
    simpa only [d2300, d3340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2300, d3340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18647 p hg
    simpa only [d2300, d3340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18761 (p : Pattern) (guard : d5539 p = 1) : d2301 p ≤ (0 : Int) + d3341 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2301, d3341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18760 p hg
    simpa only [d2301, d3341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2301, d3341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18655 p hg
    simpa only [d2301, d3341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18762 (p : Pattern) (guard : d5539 p = 1) : d2302 p ≤ (0 : Int) + d3342 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2302, d3342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18761 p hg
    simpa only [d2302, d3342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2302, d3342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18661 p hg
    simpa only [d2302, d3342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18763 (p : Pattern) (guard : d5539 p = 1) : d2303 p ≤ (0 : Int) + d3343 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2303, d3343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18762 p hg
    simpa only [d2303, d3343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2303, d3343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18684 p hg
    simpa only [d2303, d3343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18764 (p : Pattern) (guard : d5539 p = 1) : d2304 p ≤ (0 : Int) + d3344 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2304, d3344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18642 p hg
    simpa only [d2304, d3344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2304, d3344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18690 p hg
    simpa only [d2304, d3344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18765 (p : Pattern) (guard : d5539 p = 1) : d2305 p ≤ (0 : Int) + d3345 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2305, d3345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18764 p hg
    simpa only [d2305, d3345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2305, d3345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18692 p hg
    simpa only [d2305, d3345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18766 (p : Pattern) (guard : d5539 p = 1) : d2306 p ≤ (0 : Int) + d3346 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2306, d3346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18765 p hg
    simpa only [d2306, d3346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2306, d3346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18701 p hg
    simpa only [d2306, d3346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18767 (p : Pattern) (guard : d5539 p = 1) : d2307 p ≤ (0 : Int) + d3347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2307, d3347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18766 p hg
    simpa only [d2307, d3347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2307, d3347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18712 p hg
    simpa only [d2307, d3347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18768 (p : Pattern) (guard : d5539 p = 1) : d2308 p ≤ (0 : Int) + d3348 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2308, d3348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18763 p hg
    simpa only [d2308, d3348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2308, d3348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18767 p hg
    simpa only [d2308, d3348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18769 (p : Pattern) (guard : d5539 p = 1) : d2309 p ≤ (0 : Int) + d3349 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2309, d3349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18768 p hg
    simpa only [d2309, d3349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2309, d3349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18729 p hg
    simpa only [d2309, d3349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18770 (p : Pattern) (guard : d5539 p = 1) : d2310 p ≤ (0 : Int) + d3323 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2310, d3323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18729 p hg
    simpa only [d2310, d3323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2310, d3323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18743 p hg
    simpa only [d2310, d3323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18771 (p : Pattern) (guard : d5539 p = 1) : d2311 p ≤ (0 : Int) + d3350 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2311, d3350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18769 p hg
    simpa only [d2311, d3350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2311, d3350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18770 p hg
    simpa only [d2311, d3350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18772 (p : Pattern) (guard : d5539 p = 1) : d2312 p ≤ (0 : Int) + d3351 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2312, d3351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18733 p hg
    simpa only [d2312, d3351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2312, d3351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18684 p hg
    simpa only [d2312, d3351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18773 (p : Pattern) (guard : d5539 p = 1) : d2313 p ≤ (0 : Int) + d3352 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2313, d3352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18772 p hg
    simpa only [d2313, d3352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2313, d3352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18750 p hg
    simpa only [d2313, d3352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18774 (p : Pattern) (guard : d5539 p = 1) : d2314 p ≤ (0 : Int) + d3353 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2314, d3353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18773 p hg
    simpa only [d2314, d3353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2314, d3353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18729 p hg
    simpa only [d2314, d3353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18775 (p : Pattern) (guard : d5539 p = 1) : d2315 p ≤ (0 : Int) + d3354 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2315, d3354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18774 p hg
    simpa only [d2315, d3354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2315, d3354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18753 p hg
    simpa only [d2315, d3354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18776 (p : Pattern) (guard : d5539 p = 1) : d2316 p ≤ (0 : Int) + d3355 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2316, d3355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18771 p hg
    simpa only [d2316, d3355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2316, d3355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18775 p hg
    simpa only [d2316, d3355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18777 (p : Pattern) (guard : d5539 p = 1) : d2317 p ≤ (0 : Int) + d3356 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2317, d3356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18755 p hg
    simpa only [d2317, d3356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2317, d3356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18776 p hg
    simpa only [d2317, d3356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18778 (p : Pattern) (guard : d0 p = 1) : d320 p ≤ (0 : Int) + d3358 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18779 (p : Pattern) (guard : d5539 p = 1) : d2318 p ≤ (0 : Int) + d3360 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2318, d3360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17790 p hg
    simpa only [d5539, d2318, d3360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2318, d3360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18778 p hg
    simpa only [d5539, d2318, d3360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18780 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3358 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18781 (p : Pattern) (guard : d5539 p = 1) : d2319 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17789 p hg
    simpa only [d5539, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18780 p hg
    simpa only [d5539, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18782 (p : Pattern) (guard : d5539 p = 1) : d2320 p ≤ (0 : Int) + d3361 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2320, d3361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18779 p hg
    simpa only [d2320, d3361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2320, d3361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18781 p hg
    simpa only [d2320, d3361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18783 (p : Pattern) (guard : d5539 p = 1) : d2321 p ≤ (0 : Int) + d3362 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2321, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18781 p hg
    simpa only [d2321, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2321, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2321, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18784 (p : Pattern) (guard : d5539 p = 1) : d2322 p ≤ (0 : Int) + d3363 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2322, d3363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18782 p hg
    simpa only [d2322, d3363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2322, d3363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18783 p hg
    simpa only [d2322, d3363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18785 (p : Pattern) (guard : d0 p = 1) : d332 p ≤ (0 : Int) + d3358 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18786 (p : Pattern) (guard : d5539 p = 1) : d2323 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17789 p hg
    simpa only [d5539, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18785 p hg
    simpa only [d5539, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18787 (p : Pattern) (guard : d5539 p = 1) : d2324 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18786 p hg
    simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18781 p hg
    simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18788 (p : Pattern) (guard : d5539 p = 1) : d2325 p ≤ (0 : Int) + d3364 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2325, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18787 p hg
    simpa only [d2325, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2325, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18783 p hg
    simpa only [d2325, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18789 (p : Pattern) (guard : d5539 p = 1) : d2326 p ≤ (0 : Int) + d3365 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2326, d3365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18784 p hg
    simpa only [d2326, d3365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2326, d3365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18788 p hg
    simpa only [d2326, d3365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18790 (p : Pattern) (guard : d5539 p = 1) : d2327 p ≤ (0 : Int) + d3364 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2327, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18781 p hg
    simpa only [d2327, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2327, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18783 p hg
    simpa only [d2327, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18791 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3366 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18792 (p : Pattern) (guard : d5539 p = 1) : d2328 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17798 p hg
    simpa only [d5539, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18791 p hg
    simpa only [d5539, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18793 (p : Pattern) (guard : d5539 p = 1) : d2329 p ≤ (0 : Int) + d3367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2329, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18792 p hg
    simpa only [d2329, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2329, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2329, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18794 (p : Pattern) (guard : d5539 p = 1) : d2330 p ≤ (0 : Int) + d3368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2330, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18792 p hg
    simpa only [d2330, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2330, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18793 p hg
    simpa only [d2330, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18795 (p : Pattern) (guard : d5539 p = 1) : d2331 p ≤ (0 : Int) + d3369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2331, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18790 p hg
    simpa only [d2331, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2331, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18794 p hg
    simpa only [d2331, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18796 (p : Pattern) (guard : d5539 p = 1) : d2332 p ≤ (0 : Int) + d3370 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2332, d3370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18789 p hg
    simpa only [d2332, d3370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2332, d3370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18795 p hg
    simpa only [d2332, d3370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18797 (p : Pattern) (guard : d5539 p = 1) : d2333 p ≤ (0 : Int) + d3371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2333, d3371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18697 p hg
    simpa only [d2333, d3371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2333, d3371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2333, d3371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18798 (p : Pattern) (guard : d5539 p = 1) : d2334 p ≤ (0 : Int) + d3372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2334, d3372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18795 p hg
    simpa only [d2334, d3372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2334, d3372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18797 p hg
    simpa only [d2334, d3372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18799 (p : Pattern) (guard : d5539 p = 1) : d2335 p ≤ (0 : Int) + d3373 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2335, d3373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18796 p hg
    simpa only [d2335, d3373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2335, d3373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18798 p hg
    simpa only [d2335, d3373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18800 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18801 (p : Pattern) (guard : d5539 p = 1) : d2336 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17807 p hg
    simpa only [d5539, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18800 p hg
    simpa only [d5539, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18802 (p : Pattern) (guard : d5539 p = 1) : d2337 p ≤ (0 : Int) + d3375 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2337, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18801 p hg
    simpa only [d2337, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2337, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2337, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18803 (p : Pattern) (guard : d5539 p = 1) : d2338 p ≤ (0 : Int) + d3376 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2338, d3376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18781 p hg
    simpa only [d2338, d3376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2338, d3376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18802 p hg
    simpa only [d2338, d3376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18804 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3377 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18805 (p : Pattern) (guard : d5539 p = 1) : d2339 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17811 p hg
    simpa only [d5539, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18804 p hg
    simpa only [d5539, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18806 (p : Pattern) (guard : d5539 p = 1) : d2340 p ≤ (0 : Int) + d3378 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2340, d3378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18805 p hg
    simpa only [d2340, d3378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2340, d3378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2340, d3378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18807 (p : Pattern) (guard : d5539 p = 1) : d2341 p ≤ (0 : Int) + d3379 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2341, d3379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18781 p hg
    simpa only [d2341, d3379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2341, d3379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18806 p hg
    simpa only [d2341, d3379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18808 (p : Pattern) (guard : d5539 p = 1) : d2342 p ≤ (0 : Int) + d3380 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2342, d3380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18803 p hg
    simpa only [d2342, d3380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2342, d3380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18807 p hg
    simpa only [d2342, d3380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18809 (p : Pattern) (guard : d5539 p = 1) : d2343 p ≤ (0 : Int) + d3381 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2343, d3381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18781 p hg
    simpa only [d2343, d3381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2343, d3381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2343, d3381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18810 (p : Pattern) (guard : d5539 p = 1) : d2344 p ≤ (0 : Int) + d3382 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2344, d3382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18792 p hg
    simpa only [d2344, d3382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2344, d3382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2344, d3382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18811 (p : Pattern) (guard : d5539 p = 1) : d2345 p ≤ (0 : Int) + d3383 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2345, d3383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18809 p hg
    simpa only [d2345, d3383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2345, d3383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18810 p hg
    simpa only [d2345, d3383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18812 (p : Pattern) (guard : d5539 p = 1) : d2346 p ≤ (0 : Int) + d3384 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2346, d3384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18808 p hg
    simpa only [d2346, d3384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2346, d3384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18811 p hg
    simpa only [d2346, d3384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18813 (p : Pattern) (guard : d5539 p = 1) : d2347 p ≤ (0 : Int) + d3385 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2347, d3385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18707 p hg
    simpa only [d2347, d3385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2347, d3385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2347, d3385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18814 (p : Pattern) (guard : d5539 p = 1) : d2348 p ≤ (0 : Int) + d3386 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2348, d3386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18811 p hg
    simpa only [d2348, d3386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2348, d3386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18813 p hg
    simpa only [d2348, d3386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18815 (p : Pattern) (guard : d5539 p = 1) : d2349 p ≤ (0 : Int) + d3387 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2349, d3387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18812 p hg
    simpa only [d2349, d3387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2349, d3387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18814 p hg
    simpa only [d2349, d3387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18816 (p : Pattern) (guard : d5539 p = 1) : d2350 p ≤ (0 : Int) + d3388 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2350, d3388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18799 p hg
    simpa only [d2350, d3388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2350, d3388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18815 p hg
    simpa only [d2350, d3388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18817 (p : Pattern) (guard : d0 p = 1) : d330 p ≤ (0 : Int) + d3358 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18818 (p : Pattern) (guard : d5539 p = 1) : d2351 p ≤ (0 : Int) + d3391 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2351, d3391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17825 p hg
    simpa only [d5539, d2351, d3391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2351, d3391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18817 p hg
    simpa only [d5539, d2351, d3391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18819 (p : Pattern) (guard : d5539 p = 1) : d2352 p ≤ (0 : Int) + d3392 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2352, d3392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18818 p hg
    simpa only [d2352, d3392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2352, d3392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18781 p hg
    simpa only [d2352, d3392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18820 (p : Pattern) (guard : d5539 p = 1) : d2353 p ≤ (0 : Int) + d3393 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2353, d3393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18819 p hg
    simpa only [d2353, d3393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2353, d3393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18783 p hg
    simpa only [d2353, d3393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18821 (p : Pattern) (guard : d5539 p = 1) : d2354 p ≤ (0 : Int) + d3394 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2354, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18801 p hg
    simpa only [d2354, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2354, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18802 p hg
    simpa only [d2354, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18822 (p : Pattern) (guard : d5539 p = 1) : d2355 p ≤ (0 : Int) + d3395 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2355, d3395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18820 p hg
    simpa only [d2355, d3395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2355, d3395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18821 p hg
    simpa only [d2355, d3395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18823 (p : Pattern) (guard : d5539 p = 1) : d2356 p ≤ (0 : Int) + d3396 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2356, d3396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18794 p hg
    simpa only [d2356, d3396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2356, d3396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18697 p hg
    simpa only [d2356, d3396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18824 (p : Pattern) (guard : d5539 p = 1) : d2357 p ≤ (0 : Int) + d3397 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2357, d3397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18822 p hg
    simpa only [d2357, d3397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2357, d3397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18823 p hg
    simpa only [d2357, d3397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18825 (p : Pattern) (guard : d5539 p = 1) : d2358 p ≤ (0 : Int) + d3398 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2358, d3398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18794 p hg
    simpa only [d2358, d3398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2358, d3398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18699 p hg
    simpa only [d2358, d3398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18826 (p : Pattern) (guard : d5539 p = 1) : d2359 p ≤ (0 : Int) + d3399 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2359, d3399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18825 p hg
    simpa only [d2359, d3399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2359, d3399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2359, d3399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18827 (p : Pattern) (guard : d5539 p = 1) : d2360 p ≤ (0 : Int) + d3400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2360, d3400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18824 p hg
    simpa only [d2360, d3400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2360, d3400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18826 p hg
    simpa only [d2360, d3400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18828 (p : Pattern) (guard : d5539 p = 1) : d2361 p ≤ (0 : Int) + d3401 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2361, d3401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18801 p hg
    simpa only [d2361, d3401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2361, d3401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2361, d3401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18829 (p : Pattern) (guard : d5539 p = 1) : d2362 p ≤ (0 : Int) + d3402 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2362, d3402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18807 p hg
    simpa only [d2362, d3402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2362, d3402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18828 p hg
    simpa only [d2362, d3402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18830 (p : Pattern) (guard : d5539 p = 1) : d2363 p ≤ (0 : Int) + d3403 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2363, d3403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18810 p hg
    simpa only [d2363, d3403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2363, d3403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18707 p hg
    simpa only [d2363, d3403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18831 (p : Pattern) (guard : d5539 p = 1) : d2364 p ≤ (0 : Int) + d3404 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2364, d3404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18829 p hg
    simpa only [d2364, d3404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2364, d3404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18830 p hg
    simpa only [d2364, d3404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18832 (p : Pattern) (guard : d5539 p = 1) : d2365 p ≤ (0 : Int) + d3405 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2365, d3405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18810 p hg
    simpa only [d2365, d3405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2365, d3405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18709 p hg
    simpa only [d2365, d3405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18833 (p : Pattern) (guard : d5539 p = 1) : d2366 p ≤ (0 : Int) + d3406 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2366, d3406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18832 p hg
    simpa only [d2366, d3406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2366, d3406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2366, d3406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18834 (p : Pattern) (guard : d5539 p = 1) : d2367 p ≤ (0 : Int) + d3407 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2367, d3407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18831 p hg
    simpa only [d2367, d3407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2367, d3407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18833 p hg
    simpa only [d2367, d3407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18835 (p : Pattern) (guard : d5539 p = 1) : d2368 p ≤ (0 : Int) + d3408 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2368, d3408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18827 p hg
    simpa only [d2368, d3408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2368, d3408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18834 p hg
    simpa only [d2368, d3408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18836 (p : Pattern) (guard : d5539 p = 1) : d2369 p ≤ (0 : Int) + d3409 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2369, d3409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18816 p hg
    simpa only [d2369, d3409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2369, d3409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18835 p hg
    simpa only [d2369, d3409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18837 (p : Pattern) (guard : d5539 p = 1) : d2370 p ≤ (0 : Int) + d3410 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2370, d3410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18790 p hg
    simpa only [d2370, d3410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2370, d3410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18795 p hg
    simpa only [d2370, d3410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18838 (p : Pattern) (guard : d5539 p = 1) : d2371 p ≤ (0 : Int) + d3411 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2371, d3411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18837 p hg
    simpa only [d2371, d3411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2371, d3411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18798 p hg
    simpa only [d2371, d3411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18839 (p : Pattern) (guard : d5539 p = 1) : d2372 p ≤ (0 : Int) + d3412 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2372, d3412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18805 p hg
    simpa only [d2372, d3412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2372, d3412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18806 p hg
    simpa only [d2372, d3412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18840 (p : Pattern) (guard : d5539 p = 1) : d2373 p ≤ (0 : Int) + d3413 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2373, d3413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18821 p hg
    simpa only [d2373, d3413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2373, d3413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18839 p hg
    simpa only [d2373, d3413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18841 (p : Pattern) (guard : d5539 p = 1) : d2374 p ≤ (0 : Int) + d3414 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2374, d3414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18840 p hg
    simpa only [d2374, d3414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2374, d3414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2374, d3414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18842 (p : Pattern) (guard : d5539 p = 1) : d2375 p ≤ (0 : Int) + d3415 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2375, d3415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18841 p hg
    simpa only [d2375, d3415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2375, d3415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2375, d3415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18843 (p : Pattern) (guard : d5539 p = 1) : d2376 p ≤ (0 : Int) + d3416 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2376, d3416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18838 p hg
    simpa only [d2376, d3416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2376, d3416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18842 p hg
    simpa only [d2376, d3416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18844 (p : Pattern) (guard : d5539 p = 1) : d2377 p ≤ (0 : Int) + d3417 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2377, d3417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18790 p hg
    simpa only [d2377, d3417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2377, d3417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18821 p hg
    simpa only [d2377, d3417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18845 (p : Pattern) (guard : d5539 p = 1) : d2378 p ≤ (0 : Int) + d3418 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2378, d3418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18844 p hg
    simpa only [d2378, d3418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2378, d3418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18823 p hg
    simpa only [d2378, d3418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18846 (p : Pattern) (guard : d5539 p = 1) : d2379 p ≤ (0 : Int) + d3419 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2379, d3419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18845 p hg
    simpa only [d2379, d3419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2379, d3419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18826 p hg
    simpa only [d2379, d3419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18847 (p : Pattern) (guard : d5539 p = 1) : d2380 p ≤ (0 : Int) + d3420 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2380, d3420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18839 p hg
    simpa only [d2380, d3420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2380, d3420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2380, d3420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18848 (p : Pattern) (guard : d5539 p = 1) : d2381 p ≤ (0 : Int) + d3421 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2381, d3421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18847 p hg
    simpa only [d2381, d3421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2381, d3421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2381, d3421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18849 (p : Pattern) (guard : d5539 p = 1) : d2382 p ≤ (0 : Int) + d3422 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2382, d3422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18848 p hg
    simpa only [d2382, d3422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2382, d3422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2382, d3422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18850 (p : Pattern) (guard : d5539 p = 1) : d2383 p ≤ (0 : Int) + d3423 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2383, d3423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18846 p hg
    simpa only [d2383, d3423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2383, d3423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18849 p hg
    simpa only [d2383, d3423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18851 (p : Pattern) (guard : d5539 p = 1) : d2384 p ≤ (0 : Int) + d3424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2384, d3424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18843 p hg
    simpa only [d2384, d3424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2384, d3424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18850 p hg
    simpa only [d2384, d3424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18852 (p : Pattern) (guard : d5539 p = 1) : d2385 p ≤ (0 : Int) + d3425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2385, d3425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18836 p hg
    simpa only [d2385, d3425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2385, d3425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18851 p hg
    simpa only [d2385, d3425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18853 (p : Pattern) (guard : d5539 p = 1) : d2386 p ≤ (0 : Int) + d3426 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2386, d3426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18797 p hg
    simpa only [d2386, d3426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2386, d3426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2386, d3426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18854 (p : Pattern) (guard : d5539 p = 1) : d2387 p ≤ (0 : Int) + d3427 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2387, d3427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18853 p hg
    simpa only [d2387, d3427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2387, d3427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2387, d3427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18855 (p : Pattern) (guard : d5539 p = 1) : d2388 p ≤ (0 : Int) + d3428 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2388, d3428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18854 p hg
    simpa only [d2388, d3428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2388, d3428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2388, d3428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18856 (p : Pattern) (guard : d5539 p = 1) : d2389 p ≤ (0 : Int) + d3429 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2389, d3429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18855 p hg
    simpa only [d2389, d3429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2389, d3429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2389, d3429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18857 (p : Pattern) (guard : d5539 p = 1) : d2390 p ≤ (0 : Int) + d3430 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2390, d3430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18851 p hg
    simpa only [d2390, d3430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2390, d3430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18856 p hg
    simpa only [d2390, d3430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18858 (p : Pattern) (guard : d5539 p = 1) : d2391 p ≤ (0 : Int) + d3431 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2391, d3431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18852 p hg
    simpa only [d2391, d3431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2391, d3431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18857 p hg
    simpa only [d2391, d3431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18859 (p : Pattern) (guard : d5539 p = 1) : d2392 p ≤ (0 : Int) + d3364 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18788 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18790 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18860 (p : Pattern) (guard : d5539 p = 1) : d2393 p ≤ (0 : Int) + d3410 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2393, d3410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18859 p hg
    simpa only [d2393, d3410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2393, d3410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18795 p hg
    simpa only [d2393, d3410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18861 (p : Pattern) (guard : d5539 p = 1) : d2394 p ≤ (0 : Int) + d3411 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2394, d3411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18860 p hg
    simpa only [d2394, d3411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2394, d3411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18798 p hg
    simpa only [d2394, d3411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18862 (p : Pattern) (guard : d5539 p = 1) : d2395 p ≤ (0 : Int) + d3432 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2395, d3432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18861 p hg
    simpa only [d2395, d3432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2395, d3432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18815 p hg
    simpa only [d2395, d3432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18863 (p : Pattern) (guard : d5539 p = 1) : d2396 p ≤ (0 : Int) + d3433 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2396, d3433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18846 p hg
    simpa only [d2396, d3433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2396, d3433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18834 p hg
    simpa only [d2396, d3433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18864 (p : Pattern) (guard : d5539 p = 1) : d2397 p ≤ (0 : Int) + d3434 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2397, d3434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18862 p hg
    simpa only [d2397, d3434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2397, d3434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18863 p hg
    simpa only [d2397, d3434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18865 (p : Pattern) (guard : d5539 p = 1) : d2398 p ≤ (0 : Int) + d3435 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2398, d3435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18864 p hg
    simpa only [d2398, d3435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2398, d3435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18851 p hg
    simpa only [d2398, d3435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18866 (p : Pattern) (guard : d5539 p = 1) : d2399 p ≤ (0 : Int) + d3436 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2399, d3436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18851 p hg
    simpa only [d2399, d3436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2399, d3436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2399, d3436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18867 (p : Pattern) (guard : d5539 p = 1) : d2400 p ≤ (0 : Int) + d3437 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2400, d3437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18865 p hg
    simpa only [d2400, d3437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2400, d3437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18866 p hg
    simpa only [d2400, d3437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18868 (p : Pattern) (guard : d5539 p = 1) : d2401 p ≤ (0 : Int) + d3438 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2401, d3438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18858 p hg
    simpa only [d2401, d3438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2401, d3438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18867 p hg
    simpa only [d2401, d3438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18869 (p : Pattern) (guard : d5539 p = 1) : d2402 p ≤ (0 : Int) + d3439 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2402, d3439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18755 p hg
    simpa only [d2402, d3439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2402, d3439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18868 p hg
    simpa only [d2402, d3439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18870 (p : Pattern) (guard : d5539 p = 1) : d2403 p ≤ (0 : Int) + d3440 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2403, d3440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18777 p hg
    simpa only [d2403, d3440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2403, d3440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18869 p hg
    simpa only [d2403, d3440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18871 (p : Pattern) (guard : d5539 p = 1) : d2404 p ≤ (0 : Int) + d3441 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2404, d3441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18664 p hg
    simpa only [d2404, d3441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2404, d3441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18669 p hg
    simpa only [d2404, d3441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18872 (p : Pattern) (guard : d5539 p = 1) : d2405 p ≤ (0 : Int) + d3442 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2405, d3442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18690 p hg
    simpa only [d2405, d3442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2405, d3442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18871 p hg
    simpa only [d2405, d3442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18873 (p : Pattern) (guard : d5539 p = 1) : d2406 p ≤ (0 : Int) + d3443 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2406, d3443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18664 p hg
    simpa only [d2406, d3443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2406, d3443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18674 p hg
    simpa only [d2406, d3443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18874 (p : Pattern) (guard : d5539 p = 1) : d2407 p ≤ (0 : Int) + d3444 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2407, d3444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18668 p hg
    simpa only [d2407, d3444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2407, d3444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2407, d3444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18875 (p : Pattern) (guard : d5539 p = 1) : d2408 p ≤ (0 : Int) + d3445 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2408, d3445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18873 p hg
    simpa only [d2408, d3445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2408, d3445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18874 p hg
    simpa only [d2408, d3445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18876 (p : Pattern) (guard : d5539 p = 1) : d2409 p ≤ (0 : Int) + d3446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2409, d3446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18872 p hg
    simpa only [d2409, d3446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2409, d3446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18875 p hg
    simpa only [d2409, d3446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18877 (p : Pattern) (guard : d5539 p = 1) : d2410 p ≤ (0 : Int) + d3447 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2410, d3447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18703 p hg
    simpa only [d2410, d3447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2410, d3447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18874 p hg
    simpa only [d2410, d3447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18878 (p : Pattern) (guard : d5539 p = 1) : d2411 p ≤ (0 : Int) + d3448 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2411, d3448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18877 p hg
    simpa only [d2411, d3448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2411, d3448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18710 p hg
    simpa only [d2411, d3448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18879 (p : Pattern) (guard : d5539 p = 1) : d2412 p ≤ (0 : Int) + d3449 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2412, d3449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18876 p hg
    simpa only [d2412, d3449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2412, d3449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18878 p hg
    simpa only [d2412, d3449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18880 (p : Pattern) (guard : d5539 p = 1) : d2413 p ≤ (0 : Int) + d3450 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2413, d3450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18733 p hg
    simpa only [d2413, d3450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2413, d3450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18879 p hg
    simpa only [d2413, d3450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18881 (p : Pattern) (guard : d5539 p = 1) : d2414 p ≤ (0 : Int) + d3451 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2414, d3451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18871 p hg
    simpa only [d2414, d3451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2414, d3451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18676 p hg
    simpa only [d2414, d3451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18882 (p : Pattern) (guard : d5539 p = 1) : d2415 p ≤ (0 : Int) + d3452 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2415, d3452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18874 p hg
    simpa only [d2415, d3452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2415, d3452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18709 p hg
    simpa only [d2415, d3452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18883 (p : Pattern) (guard : d5539 p = 1) : d2416 p ≤ (0 : Int) + d3453 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2416, d3453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18881 p hg
    simpa only [d2416, d3453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2416, d3453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18882 p hg
    simpa only [d2416, d3453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18884 (p : Pattern) (guard : d5539 p = 1) : d2417 p ≤ (0 : Int) + d3454 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2417, d3454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18874 p hg
    simpa only [d2417, d3454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2417, d3454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2417, d3454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18885 (p : Pattern) (guard : d5539 p = 1) : d2418 p ≤ (0 : Int) + d3455 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2418, d3455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18884 p hg
    simpa only [d2418, d3455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2418, d3455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2418, d3455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18886 (p : Pattern) (guard : d5539 p = 1) : d2419 p ≤ (0 : Int) + d3456 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2419, d3456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18883 p hg
    simpa only [d2419, d3456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2419, d3456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18885 p hg
    simpa only [d2419, d3456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18887 (p : Pattern) (guard : d5539 p = 1) : d2420 p ≤ (0 : Int) + d3457 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2420, d3457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18724 p hg
    simpa only [d2420, d3457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2420, d3457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18886 p hg
    simpa only [d2420, d3457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18888 (p : Pattern) (guard : d5539 p = 1) : d2421 p ≤ (0 : Int) + d3458 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2421, d3458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18880 p hg
    simpa only [d2421, d3458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2421, d3458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18887 p hg
    simpa only [d2421, d3458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18889 (p : Pattern) (guard : d5539 p = 1) : d2422 p ≤ (0 : Int) + d3459 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2422, d3459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18654 p hg
    simpa only [d2422, d3459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2422, d3459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18718 p hg
    simpa only [d2422, d3459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18890 (p : Pattern) (guard : d5539 p = 1) : d2423 p ≤ (0 : Int) + d3460 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2423, d3460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18889 p hg
    simpa only [d2423, d3460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2423, d3460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18719 p hg
    simpa only [d2423, d3460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18891 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3461 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18892 (p : Pattern) (guard : d5539 p = 1) : d2424 p ≤ (0 : Int) + d3461 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17897 p hg
    simpa only [d5539, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18891 p hg
    simpa only [d5539, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18893 (p : Pattern) (guard : d5539 p = 1) : d2425 p ≤ (0 : Int) + d3462 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2425, d3462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18892 p hg
    simpa only [d2425, d3462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2425, d3462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2425, d3462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18894 (p : Pattern) (guard : d5539 p = 1) : d2426 p ≤ (0 : Int) + d3463 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2426, d3463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18892 p hg
    simpa only [d2426, d3463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2426, d3463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18893 p hg
    simpa only [d2426, d3463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18895 (p : Pattern) (guard : d5539 p = 1) : d2427 p ≤ (0 : Int) + d3464 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2427, d3464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18651 p hg
    simpa only [d2427, d3464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2427, d3464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18894 p hg
    simpa only [d2427, d3464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18896 (p : Pattern) (guard : d5539 p = 1) : d2428 p ≤ (0 : Int) + d3465 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2428, d3465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18895 p hg
    simpa only [d2428, d3465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2428, d3465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2428, d3465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18897 (p : Pattern) (guard : d5539 p = 1) : d2429 p ≤ (0 : Int) + d3466 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2429, d3466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18896 p hg
    simpa only [d2429, d3466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2429, d3466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2429, d3466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18898 (p : Pattern) (guard : d5539 p = 1) : d2430 p ≤ (0 : Int) + d3467 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2430, d3467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18890 p hg
    simpa only [d2430, d3467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2430, d3467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18897 p hg
    simpa only [d2430, d3467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18899 (p : Pattern) (guard : d5539 p = 1) : d2431 p ≤ (0 : Int) + d3468 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2431, d3468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18651 p hg
    simpa only [d2431, d3468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2431, d3468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18699 p hg
    simpa only [d2431, d3468, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
