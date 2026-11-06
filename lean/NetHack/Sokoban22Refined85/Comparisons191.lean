/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons190
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare26740 (p : Pattern) (guard : d5539 p = 1) : d3332 p ≤ (0 : Int) + d2294 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3332, d2294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26716 p hg
    simpa only [d3332, d2294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3332, d2294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3332, d2294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26741 (p : Pattern) (guard : d5539 p = 1) : d3333 p ≤ (0 : Int) + d2295 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3333, d2295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26739 p hg
    simpa only [d3333, d2295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3333, d2295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26740 p hg
    simpa only [d3333, d2295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26742 (p : Pattern) (guard : d5539 p = 1) : d3334 p ≤ (0 : Int) + d2296 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3334, d2296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26732 p hg
    simpa only [d3334, d2296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3334, d2296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26741 p hg
    simpa only [d3334, d2296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26743 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26744 (p : Pattern) (guard : d5268 p = 1) : d3335 p ≤ (0 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3335, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5268, d3335, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3335, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26743 p hg
    simpa only [d5268, d3335, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26745 (p : Pattern) (guard : d5268 p = 1) : d3336 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26744 p hg
    simpa only [d3336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d3336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26746 (p : Pattern) (guard : d0 p = 1) : d3226 p ≤ (0 : Int) + d320 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26747 (p : Pattern) (guard : d5539 p = 1) : d3337 p ≤ (0 : Int) + d2297 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d3337, d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26745 p hg
    simpa only [d5539, d3337, d2297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d3337, d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26746 p hg
    simpa only [d5539, d3337, d2297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26748 (p : Pattern) (guard : d5539 p = 1) : d3338 p ≤ (0 : Int) + d2298 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3338, d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26747 p hg
    simpa only [d3338, d2298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3338, d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26610 p hg
    simpa only [d3338, d2298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26749 (p : Pattern) (guard : d5539 p = 1) : d3339 p ≤ (0 : Int) + d2299 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3339, d2299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26748 p hg
    simpa only [d3339, d2299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3339, d2299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26612 p hg
    simpa only [d3339, d2299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26750 (p : Pattern) (guard : d5539 p = 1) : d3340 p ≤ (0 : Int) + d2300 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3340, d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26749 p hg
    simpa only [d3340, d2300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3340, d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26625 p hg
    simpa only [d3340, d2300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26751 (p : Pattern) (guard : d5539 p = 1) : d3341 p ≤ (0 : Int) + d2301 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3341, d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26750 p hg
    simpa only [d3341, d2301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3341, d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26634 p hg
    simpa only [d3341, d2301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26752 (p : Pattern) (guard : d5539 p = 1) : d3342 p ≤ (0 : Int) + d2302 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3342, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26751 p hg
    simpa only [d3342, d2302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3342, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26641 p hg
    simpa only [d3342, d2302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26753 (p : Pattern) (guard : d5539 p = 1) : d3343 p ≤ (0 : Int) + d2303 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3343, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26752 p hg
    simpa only [d3343, d2303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3343, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26667 p hg
    simpa only [d3343, d2303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26754 (p : Pattern) (guard : d5539 p = 1) : d3344 p ≤ (0 : Int) + d2304 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3344, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26620 p hg
    simpa only [d3344, d2304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3344, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26676 p hg
    simpa only [d3344, d2304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26755 (p : Pattern) (guard : d5539 p = 1) : d3345 p ≤ (0 : Int) + d2305 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3345, d2305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26754 p hg
    simpa only [d3345, d2305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3345, d2305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26678 p hg
    simpa only [d3345, d2305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26756 (p : Pattern) (guard : d5539 p = 1) : d3346 p ≤ (0 : Int) + d2306 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3346, d2306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26755 p hg
    simpa only [d3346, d2306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3346, d2306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26688 p hg
    simpa only [d3346, d2306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26757 (p : Pattern) (guard : d5539 p = 1) : d3347 p ≤ (0 : Int) + d2307 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3347, d2307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26756 p hg
    simpa only [d3347, d2307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3347, d2307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26699 p hg
    simpa only [d3347, d2307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26758 (p : Pattern) (guard : d5539 p = 1) : d3348 p ≤ (0 : Int) + d2308 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3348, d2308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26753 p hg
    simpa only [d3348, d2308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3348, d2308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26757 p hg
    simpa only [d3348, d2308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26759 (p : Pattern) (guard : d5539 p = 1) : d3349 p ≤ (0 : Int) + d2309 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3349, d2309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26758 p hg
    simpa only [d3349, d2309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3349, d2309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26716 p hg
    simpa only [d3349, d2309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26760 (p : Pattern) (guard : d5539 p = 1) : d3323 p ≤ (0 : Int) + d2310 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3323, d2310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26716 p hg
    simpa only [d3323, d2310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3323, d2310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26730 p hg
    simpa only [d3323, d2310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26761 (p : Pattern) (guard : d5539 p = 1) : d3350 p ≤ (0 : Int) + d2311 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3350, d2311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26759 p hg
    simpa only [d3350, d2311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3350, d2311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26760 p hg
    simpa only [d3350, d2311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26762 (p : Pattern) (guard : d5539 p = 1) : d3351 p ≤ (0 : Int) + d2312 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3351, d2312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26720 p hg
    simpa only [d3351, d2312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3351, d2312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26667 p hg
    simpa only [d3351, d2312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26763 (p : Pattern) (guard : d5539 p = 1) : d3352 p ≤ (0 : Int) + d2313 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3352, d2313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26762 p hg
    simpa only [d3352, d2313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3352, d2313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26737 p hg
    simpa only [d3352, d2313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26764 (p : Pattern) (guard : d5539 p = 1) : d3353 p ≤ (0 : Int) + d2314 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3353, d2314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26763 p hg
    simpa only [d3353, d2314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3353, d2314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26716 p hg
    simpa only [d3353, d2314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26765 (p : Pattern) (guard : d5539 p = 1) : d3354 p ≤ (0 : Int) + d2315 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3354, d2315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26764 p hg
    simpa only [d3354, d2315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3354, d2315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26740 p hg
    simpa only [d3354, d2315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26766 (p : Pattern) (guard : d5539 p = 1) : d3355 p ≤ (0 : Int) + d2316 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3355, d2316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26761 p hg
    simpa only [d3355, d2316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3355, d2316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26765 p hg
    simpa only [d3355, d2316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26767 (p : Pattern) (guard : d5539 p = 1) : d3356 p ≤ (0 : Int) + d2317 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3356, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26742 p hg
    simpa only [d3356, d2317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3356, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26766 p hg
    simpa only [d3356, d2317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26768 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26769 (p : Pattern) (guard : d5268 p = 1) : d3357 p ≤ (0 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3357, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5268, d3357, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3357, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26768 p hg
    simpa only [d5268, d3357, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26770 (p : Pattern) (guard : d5268 p = 1) : d3358 p ≤ (0 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3358, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5268, d3358, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3358, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20160 p hg
    simpa only [d5268, d3358, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26771 (p : Pattern) (guard : d5268 p = 1) : d3359 p ≤ (0 : Int) + d103 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26769 p hg
    simpa only [d3359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26770 p hg
    simpa only [d3359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26772 (p : Pattern) (guard : d0 p = 1) : d3358 p ≤ (0 : Int) + d320 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26773 (p : Pattern) (guard : d5539 p = 1) : d3360 p ≤ (0 : Int) + d2318 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d3360, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26771 p hg
    simpa only [d5539, d3360, d2318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d3360, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26772 p hg
    simpa only [d5539, d3360, d2318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26774 (p : Pattern) (guard : d0 p = 1) : d3358 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26775 (p : Pattern) (guard : d5539 p = 1) : d3358 p ≤ (0 : Int) + d2319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26770 p hg
    simpa only [d5539, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d5539, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26776 (p : Pattern) (guard : d5539 p = 1) : d3361 p ≤ (0 : Int) + d2320 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3361, d2320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26773 p hg
    simpa only [d3361, d2320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3361, d2320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26775 p hg
    simpa only [d3361, d2320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26777 (p : Pattern) (guard : d5539 p = 1) : d3362 p ≤ (0 : Int) + d2321 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3362, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26775 p hg
    simpa only [d3362, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3362, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3362, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26778 (p : Pattern) (guard : d5539 p = 1) : d3363 p ≤ (0 : Int) + d2322 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3363, d2322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26776 p hg
    simpa only [d3363, d2322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3363, d2322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26777 p hg
    simpa only [d3363, d2322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26779 (p : Pattern) (guard : d0 p = 1) : d3358 p ≤ (0 : Int) + d332 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26780 (p : Pattern) (guard : d5539 p = 1) : d3358 p ≤ (0 : Int) + d2323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26770 p hg
    simpa only [d5539, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26779 p hg
    simpa only [d5539, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26781 (p : Pattern) (guard : d5539 p = 1) : d3358 p ≤ (0 : Int) + d2324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26780 p hg
    simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26775 p hg
    simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26782 (p : Pattern) (guard : d5539 p = 1) : d3364 p ≤ (0 : Int) + d2325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3364, d2325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26781 p hg
    simpa only [d3364, d2325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3364, d2325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26777 p hg
    simpa only [d3364, d2325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26783 (p : Pattern) (guard : d5539 p = 1) : d3365 p ≤ (0 : Int) + d2326 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3365, d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26778 p hg
    simpa only [d3365, d2326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3365, d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26782 p hg
    simpa only [d3365, d2326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26784 (p : Pattern) (guard : d5539 p = 1) : d3364 p ≤ (0 : Int) + d2327 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3364, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26775 p hg
    simpa only [d3364, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3364, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26777 p hg
    simpa only [d3364, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26785 (p : Pattern) (guard : d5268 p = 1) : d3366 p ≤ (0 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3366, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14654 p hg
    simpa only [d5268, d3366, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3366, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20170 p hg
    simpa only [d5268, d3366, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26786 (p : Pattern) (guard : d0 p = 1) : d3366 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26787 (p : Pattern) (guard : d5539 p = 1) : d3366 p ≤ (0 : Int) + d2328 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26785 p hg
    simpa only [d5539, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d5539, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26788 (p : Pattern) (guard : d5539 p = 1) : d3367 p ≤ (0 : Int) + d2329 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3367, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26787 p hg
    simpa only [d3367, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3367, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3367, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26789 (p : Pattern) (guard : d5539 p = 1) : d3368 p ≤ (0 : Int) + d2330 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3368, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26787 p hg
    simpa only [d3368, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3368, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26788 p hg
    simpa only [d3368, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26790 (p : Pattern) (guard : d5539 p = 1) : d3369 p ≤ (0 : Int) + d2331 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3369, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26784 p hg
    simpa only [d3369, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3369, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26789 p hg
    simpa only [d3369, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26791 (p : Pattern) (guard : d5539 p = 1) : d3370 p ≤ (0 : Int) + d2332 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3370, d2332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26783 p hg
    simpa only [d3370, d2332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3370, d2332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26790 p hg
    simpa only [d3370, d2332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26792 (p : Pattern) (guard : d5539 p = 1) : d3371 p ≤ (0 : Int) + d2333 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3371, d2333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26684 p hg
    simpa only [d3371, d2333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3371, d2333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3371, d2333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26793 (p : Pattern) (guard : d5539 p = 1) : d3372 p ≤ (0 : Int) + d2334 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3372, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26790 p hg
    simpa only [d3372, d2334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3372, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26792 p hg
    simpa only [d3372, d2334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26794 (p : Pattern) (guard : d5539 p = 1) : d3373 p ≤ (0 : Int) + d2335 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3373, d2335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26791 p hg
    simpa only [d3373, d2335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3373, d2335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26793 p hg
    simpa only [d3373, d2335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26795 (p : Pattern) (guard : d5268 p = 1) : d3374 p ≤ (0 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3374, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d5268, d3374, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3374, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20238 p hg
    simpa only [d5268, d3374, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26796 (p : Pattern) (guard : d0 p = 1) : d3374 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26797 (p : Pattern) (guard : d5539 p = 1) : d3374 p ≤ (0 : Int) + d2336 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26795 p hg
    simpa only [d5539, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d5539, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26798 (p : Pattern) (guard : d5539 p = 1) : d3375 p ≤ (0 : Int) + d2337 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3375, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26797 p hg
    simpa only [d3375, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3375, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3375, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26799 (p : Pattern) (guard : d5539 p = 1) : d3376 p ≤ (0 : Int) + d2338 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3376, d2338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26775 p hg
    simpa only [d3376, d2338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3376, d2338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26798 p hg
    simpa only [d3376, d2338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26800 (p : Pattern) (guard : d5268 p = 1) : d3377 p ≤ (0 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3377, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14675 p hg
    simpa only [d5268, d3377, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3377, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20290 p hg
    simpa only [d5268, d3377, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26801 (p : Pattern) (guard : d0 p = 1) : d3377 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26802 (p : Pattern) (guard : d5539 p = 1) : d3377 p ≤ (0 : Int) + d2339 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26800 p hg
    simpa only [d5539, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26801 p hg
    simpa only [d5539, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26803 (p : Pattern) (guard : d5539 p = 1) : d3378 p ≤ (0 : Int) + d2340 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3378, d2340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26802 p hg
    simpa only [d3378, d2340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3378, d2340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3378, d2340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26804 (p : Pattern) (guard : d5539 p = 1) : d3379 p ≤ (0 : Int) + d2341 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3379, d2341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26775 p hg
    simpa only [d3379, d2341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3379, d2341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26803 p hg
    simpa only [d3379, d2341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26805 (p : Pattern) (guard : d5539 p = 1) : d3380 p ≤ (0 : Int) + d2342 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3380, d2342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26799 p hg
    simpa only [d3380, d2342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3380, d2342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26804 p hg
    simpa only [d3380, d2342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26806 (p : Pattern) (guard : d5539 p = 1) : d3381 p ≤ (0 : Int) + d2343 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3381, d2343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26775 p hg
    simpa only [d3381, d2343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3381, d2343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3381, d2343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26807 (p : Pattern) (guard : d5539 p = 1) : d3382 p ≤ (0 : Int) + d2344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3382, d2344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26787 p hg
    simpa only [d3382, d2344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3382, d2344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3382, d2344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26808 (p : Pattern) (guard : d5539 p = 1) : d3383 p ≤ (0 : Int) + d2345 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3383, d2345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26806 p hg
    simpa only [d3383, d2345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3383, d2345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26807 p hg
    simpa only [d3383, d2345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26809 (p : Pattern) (guard : d5539 p = 1) : d3384 p ≤ (0 : Int) + d2346 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3384, d2346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26805 p hg
    simpa only [d3384, d2346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3384, d2346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26808 p hg
    simpa only [d3384, d2346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26810 (p : Pattern) (guard : d5539 p = 1) : d3385 p ≤ (0 : Int) + d2347 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3385, d2347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26694 p hg
    simpa only [d3385, d2347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3385, d2347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3385, d2347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26811 (p : Pattern) (guard : d5539 p = 1) : d3386 p ≤ (0 : Int) + d2348 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3386, d2348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26808 p hg
    simpa only [d3386, d2348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3386, d2348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26810 p hg
    simpa only [d3386, d2348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26812 (p : Pattern) (guard : d5539 p = 1) : d3387 p ≤ (0 : Int) + d2349 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3387, d2349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26809 p hg
    simpa only [d3387, d2349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3387, d2349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26811 p hg
    simpa only [d3387, d2349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26813 (p : Pattern) (guard : d5539 p = 1) : d3388 p ≤ (0 : Int) + d2350 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3388, d2350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26794 p hg
    simpa only [d3388, d2350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3388, d2350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26812 p hg
    simpa only [d3388, d2350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26814 (p : Pattern) (guard : d0 p = 1) : d39 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26815 (p : Pattern) (guard : d5268 p = 1) : d3389 p ≤ (0 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3389, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5268, d3389, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3389, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26814 p hg
    simpa only [d5268, d3389, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26816 (p : Pattern) (guard : d5268 p = 1) : d3390 p ≤ (0 : Int) + d103 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26815 p hg
    simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26770 p hg
    simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26817 (p : Pattern) (guard : d0 p = 1) : d3358 p ≤ (0 : Int) + d330 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26818 (p : Pattern) (guard : d5539 p = 1) : d3391 p ≤ (0 : Int) + d2351 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d3391, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26816 p hg
    simpa only [d5539, d3391, d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d3391, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26817 p hg
    simpa only [d5539, d3391, d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26819 (p : Pattern) (guard : d5539 p = 1) : d3392 p ≤ (0 : Int) + d2352 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3392, d2352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26818 p hg
    simpa only [d3392, d2352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3392, d2352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26775 p hg
    simpa only [d3392, d2352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26820 (p : Pattern) (guard : d5539 p = 1) : d3393 p ≤ (0 : Int) + d2353 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3393, d2353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26819 p hg
    simpa only [d3393, d2353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3393, d2353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26777 p hg
    simpa only [d3393, d2353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26821 (p : Pattern) (guard : d5539 p = 1) : d3394 p ≤ (0 : Int) + d2354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3394, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26797 p hg
    simpa only [d3394, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3394, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26798 p hg
    simpa only [d3394, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26822 (p : Pattern) (guard : d5539 p = 1) : d3395 p ≤ (0 : Int) + d2355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3395, d2355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26820 p hg
    simpa only [d3395, d2355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3395, d2355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26821 p hg
    simpa only [d3395, d2355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26823 (p : Pattern) (guard : d5539 p = 1) : d3396 p ≤ (0 : Int) + d2356 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3396, d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26789 p hg
    simpa only [d3396, d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3396, d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26684 p hg
    simpa only [d3396, d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26824 (p : Pattern) (guard : d5539 p = 1) : d3397 p ≤ (0 : Int) + d2357 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3397, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26822 p hg
    simpa only [d3397, d2357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3397, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26823 p hg
    simpa only [d3397, d2357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26825 (p : Pattern) (guard : d5539 p = 1) : d3398 p ≤ (0 : Int) + d2358 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3398, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26789 p hg
    simpa only [d3398, d2358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3398, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26686 p hg
    simpa only [d3398, d2358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26826 (p : Pattern) (guard : d5539 p = 1) : d3399 p ≤ (0 : Int) + d2359 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3399, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26825 p hg
    simpa only [d3399, d2359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3399, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3399, d2359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26827 (p : Pattern) (guard : d5539 p = 1) : d3400 p ≤ (0 : Int) + d2360 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3400, d2360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26824 p hg
    simpa only [d3400, d2360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3400, d2360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26826 p hg
    simpa only [d3400, d2360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26828 (p : Pattern) (guard : d5539 p = 1) : d3401 p ≤ (0 : Int) + d2361 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3401, d2361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26797 p hg
    simpa only [d3401, d2361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3401, d2361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3401, d2361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26829 (p : Pattern) (guard : d5539 p = 1) : d3402 p ≤ (0 : Int) + d2362 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3402, d2362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26804 p hg
    simpa only [d3402, d2362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3402, d2362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26828 p hg
    simpa only [d3402, d2362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26830 (p : Pattern) (guard : d5539 p = 1) : d3403 p ≤ (0 : Int) + d2363 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3403, d2363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26807 p hg
    simpa only [d3403, d2363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3403, d2363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26694 p hg
    simpa only [d3403, d2363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26831 (p : Pattern) (guard : d5539 p = 1) : d3404 p ≤ (0 : Int) + d2364 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3404, d2364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26829 p hg
    simpa only [d3404, d2364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3404, d2364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26830 p hg
    simpa only [d3404, d2364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26832 (p : Pattern) (guard : d5539 p = 1) : d3405 p ≤ (0 : Int) + d2365 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3405, d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26807 p hg
    simpa only [d3405, d2365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3405, d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26696 p hg
    simpa only [d3405, d2365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26833 (p : Pattern) (guard : d5539 p = 1) : d3406 p ≤ (0 : Int) + d2366 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3406, d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26832 p hg
    simpa only [d3406, d2366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3406, d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3406, d2366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26834 (p : Pattern) (guard : d5539 p = 1) : d3407 p ≤ (0 : Int) + d2367 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3407, d2367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26831 p hg
    simpa only [d3407, d2367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3407, d2367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26833 p hg
    simpa only [d3407, d2367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26835 (p : Pattern) (guard : d5539 p = 1) : d3408 p ≤ (0 : Int) + d2368 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3408, d2368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26827 p hg
    simpa only [d3408, d2368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3408, d2368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26834 p hg
    simpa only [d3408, d2368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26836 (p : Pattern) (guard : d5539 p = 1) : d3409 p ≤ (0 : Int) + d2369 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3409, d2369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26813 p hg
    simpa only [d3409, d2369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3409, d2369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26835 p hg
    simpa only [d3409, d2369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26837 (p : Pattern) (guard : d5539 p = 1) : d3410 p ≤ (0 : Int) + d2370 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3410, d2370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26784 p hg
    simpa only [d3410, d2370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3410, d2370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26790 p hg
    simpa only [d3410, d2370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26838 (p : Pattern) (guard : d5539 p = 1) : d3411 p ≤ (0 : Int) + d2371 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3411, d2371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26837 p hg
    simpa only [d3411, d2371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3411, d2371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26793 p hg
    simpa only [d3411, d2371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26839 (p : Pattern) (guard : d5539 p = 1) : d3412 p ≤ (0 : Int) + d2372 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3412, d2372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26802 p hg
    simpa only [d3412, d2372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3412, d2372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26803 p hg
    simpa only [d3412, d2372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26840 (p : Pattern) (guard : d5539 p = 1) : d3413 p ≤ (0 : Int) + d2373 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3413, d2373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26821 p hg
    simpa only [d3413, d2373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3413, d2373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26839 p hg
    simpa only [d3413, d2373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26841 (p : Pattern) (guard : d5539 p = 1) : d3414 p ≤ (0 : Int) + d2374 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3414, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26840 p hg
    simpa only [d3414, d2374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3414, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3414, d2374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26842 (p : Pattern) (guard : d5539 p = 1) : d3415 p ≤ (0 : Int) + d2375 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3415, d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26841 p hg
    simpa only [d3415, d2375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3415, d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3415, d2375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26843 (p : Pattern) (guard : d5539 p = 1) : d3416 p ≤ (0 : Int) + d2376 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3416, d2376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26838 p hg
    simpa only [d3416, d2376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3416, d2376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26842 p hg
    simpa only [d3416, d2376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26844 (p : Pattern) (guard : d5539 p = 1) : d3417 p ≤ (0 : Int) + d2377 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3417, d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26784 p hg
    simpa only [d3417, d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3417, d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26821 p hg
    simpa only [d3417, d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26845 (p : Pattern) (guard : d5539 p = 1) : d3418 p ≤ (0 : Int) + d2378 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3418, d2378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26844 p hg
    simpa only [d3418, d2378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3418, d2378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26823 p hg
    simpa only [d3418, d2378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26846 (p : Pattern) (guard : d5539 p = 1) : d3419 p ≤ (0 : Int) + d2379 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3419, d2379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26845 p hg
    simpa only [d3419, d2379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3419, d2379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26826 p hg
    simpa only [d3419, d2379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26847 (p : Pattern) (guard : d5539 p = 1) : d3420 p ≤ (0 : Int) + d2380 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3420, d2380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26839 p hg
    simpa only [d3420, d2380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3420, d2380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3420, d2380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26848 (p : Pattern) (guard : d5539 p = 1) : d3421 p ≤ (0 : Int) + d2381 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3421, d2381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26847 p hg
    simpa only [d3421, d2381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3421, d2381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3421, d2381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26849 (p : Pattern) (guard : d5539 p = 1) : d3422 p ≤ (0 : Int) + d2382 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3422, d2382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26848 p hg
    simpa only [d3422, d2382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3422, d2382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3422, d2382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26850 (p : Pattern) (guard : d5539 p = 1) : d3423 p ≤ (0 : Int) + d2383 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3423, d2383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26846 p hg
    simpa only [d3423, d2383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3423, d2383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26849 p hg
    simpa only [d3423, d2383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26851 (p : Pattern) (guard : d5539 p = 1) : d3424 p ≤ (0 : Int) + d2384 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3424, d2384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26843 p hg
    simpa only [d3424, d2384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3424, d2384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26850 p hg
    simpa only [d3424, d2384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26852 (p : Pattern) (guard : d5539 p = 1) : d3425 p ≤ (0 : Int) + d2385 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3425, d2385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26836 p hg
    simpa only [d3425, d2385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3425, d2385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26851 p hg
    simpa only [d3425, d2385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26853 (p : Pattern) (guard : d5539 p = 1) : d3426 p ≤ (0 : Int) + d2386 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3426, d2386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26792 p hg
    simpa only [d3426, d2386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3426, d2386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3426, d2386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26854 (p : Pattern) (guard : d5539 p = 1) : d3427 p ≤ (0 : Int) + d2387 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3427, d2387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26853 p hg
    simpa only [d3427, d2387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3427, d2387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3427, d2387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26855 (p : Pattern) (guard : d5539 p = 1) : d3428 p ≤ (0 : Int) + d2388 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3428, d2388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26854 p hg
    simpa only [d3428, d2388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3428, d2388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3428, d2388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26856 (p : Pattern) (guard : d5539 p = 1) : d3429 p ≤ (0 : Int) + d2389 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3429, d2389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26855 p hg
    simpa only [d3429, d2389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3429, d2389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3429, d2389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26857 (p : Pattern) (guard : d5539 p = 1) : d3430 p ≤ (0 : Int) + d2390 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3430, d2390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26851 p hg
    simpa only [d3430, d2390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3430, d2390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26856 p hg
    simpa only [d3430, d2390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26858 (p : Pattern) (guard : d5539 p = 1) : d3431 p ≤ (0 : Int) + d2391 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3431, d2391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26852 p hg
    simpa only [d3431, d2391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3431, d2391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26857 p hg
    simpa only [d3431, d2391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26859 (p : Pattern) (guard : d5539 p = 1) : d3364 p ≤ (0 : Int) + d2392 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26782 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26784 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26860 (p : Pattern) (guard : d5539 p = 1) : d3410 p ≤ (0 : Int) + d2393 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3410, d2393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26859 p hg
    simpa only [d3410, d2393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3410, d2393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26790 p hg
    simpa only [d3410, d2393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26861 (p : Pattern) (guard : d5539 p = 1) : d3411 p ≤ (0 : Int) + d2394 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3411, d2394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26860 p hg
    simpa only [d3411, d2394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3411, d2394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26793 p hg
    simpa only [d3411, d2394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26862 (p : Pattern) (guard : d5539 p = 1) : d3432 p ≤ (0 : Int) + d2395 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3432, d2395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26861 p hg
    simpa only [d3432, d2395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3432, d2395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26812 p hg
    simpa only [d3432, d2395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26863 (p : Pattern) (guard : d5539 p = 1) : d3433 p ≤ (0 : Int) + d2396 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3433, d2396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26846 p hg
    simpa only [d3433, d2396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3433, d2396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26834 p hg
    simpa only [d3433, d2396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26864 (p : Pattern) (guard : d5539 p = 1) : d3434 p ≤ (0 : Int) + d2397 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3434, d2397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26862 p hg
    simpa only [d3434, d2397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3434, d2397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26863 p hg
    simpa only [d3434, d2397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26865 (p : Pattern) (guard : d5539 p = 1) : d3435 p ≤ (0 : Int) + d2398 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3435, d2398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26864 p hg
    simpa only [d3435, d2398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3435, d2398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26851 p hg
    simpa only [d3435, d2398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26866 (p : Pattern) (guard : d5539 p = 1) : d3436 p ≤ (0 : Int) + d2399 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3436, d2399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26851 p hg
    simpa only [d3436, d2399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3436, d2399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3436, d2399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26867 (p : Pattern) (guard : d5539 p = 1) : d3437 p ≤ (0 : Int) + d2400 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3437, d2400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26865 p hg
    simpa only [d3437, d2400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3437, d2400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26866 p hg
    simpa only [d3437, d2400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26868 (p : Pattern) (guard : d5539 p = 1) : d3438 p ≤ (0 : Int) + d2401 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3438, d2401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26858 p hg
    simpa only [d3438, d2401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3438, d2401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26867 p hg
    simpa only [d3438, d2401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26869 (p : Pattern) (guard : d5539 p = 1) : d3439 p ≤ (0 : Int) + d2402 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3439, d2402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26742 p hg
    simpa only [d3439, d2402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3439, d2402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26868 p hg
    simpa only [d3439, d2402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26870 (p : Pattern) (guard : d5539 p = 1) : d3440 p ≤ (0 : Int) + d2403 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3440, d2403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26767 p hg
    simpa only [d3440, d2403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3440, d2403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26869 p hg
    simpa only [d3440, d2403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26871 (p : Pattern) (guard : d5539 p = 1) : d3441 p ≤ (0 : Int) + d2404 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3441, d2404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26645 p hg
    simpa only [d3441, d2404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3441, d2404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26651 p hg
    simpa only [d3441, d2404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26872 (p : Pattern) (guard : d5539 p = 1) : d3442 p ≤ (0 : Int) + d2405 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3442, d2405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26676 p hg
    simpa only [d3442, d2405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3442, d2405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26871 p hg
    simpa only [d3442, d2405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26873 (p : Pattern) (guard : d5539 p = 1) : d3443 p ≤ (0 : Int) + d2406 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3443, d2406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26645 p hg
    simpa only [d3443, d2406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3443, d2406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26657 p hg
    simpa only [d3443, d2406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26874 (p : Pattern) (guard : d5539 p = 1) : d3444 p ≤ (0 : Int) + d2407 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3444, d2407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26650 p hg
    simpa only [d3444, d2407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3444, d2407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3444, d2407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26875 (p : Pattern) (guard : d5539 p = 1) : d3445 p ≤ (0 : Int) + d2408 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3445, d2408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26873 p hg
    simpa only [d3445, d2408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3445, d2408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26874 p hg
    simpa only [d3445, d2408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26876 (p : Pattern) (guard : d5539 p = 1) : d3446 p ≤ (0 : Int) + d2409 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3446, d2409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26872 p hg
    simpa only [d3446, d2409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3446, d2409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26875 p hg
    simpa only [d3446, d2409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26877 (p : Pattern) (guard : d5539 p = 1) : d3447 p ≤ (0 : Int) + d2410 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3447, d2410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26690 p hg
    simpa only [d3447, d2410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3447, d2410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26874 p hg
    simpa only [d3447, d2410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26878 (p : Pattern) (guard : d5539 p = 1) : d3448 p ≤ (0 : Int) + d2411 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3448, d2411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26877 p hg
    simpa only [d3448, d2411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3448, d2411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26697 p hg
    simpa only [d3448, d2411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26879 (p : Pattern) (guard : d5539 p = 1) : d3449 p ≤ (0 : Int) + d2412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3449, d2412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26876 p hg
    simpa only [d3449, d2412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3449, d2412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26878 p hg
    simpa only [d3449, d2412, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
