/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons205
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare28840 (p : Pattern) (guard : d5854 p = 1) : d3279 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26681 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28841 (p : Pattern) (guard : d5855 p = 1) : d3279 p ≤ (0 : Int) + d2578 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28836 p hg
    simpa only [d5855, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28840 p hg
    simpa only [d5855, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28842 (p : Pattern) (guard : d5855 p = 1) : d3279 p ≤ (0 : Int) + d2579 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28839 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28841 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28843 (p : Pattern) (guard : d5855 p = 1) : d3280 p ≤ (0 : Int) + d2580 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3280, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28841 p hg
    simpa only [d3280, d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3280, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3280, d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28844 (p : Pattern) (guard : d5855 p = 1) : d3281 p ≤ (0 : Int) + d2581 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3281, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28842 p hg
    simpa only [d3281, d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3281, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28843 p hg
    simpa only [d3281, d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28845 (p : Pattern) (guard : d5855 p = 1) : d3282 p ≤ (0 : Int) + d2582 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3282, d2582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28765 p hg
    simpa only [d3282, d2582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3282, d2582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28844 p hg
    simpa only [d3282, d2582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28846 (p : Pattern) (guard : d5847 p = 1) : d3257 p ≤ (0 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3257, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23502 p hg
    simpa only [d5847, d3257, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3257, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20007 p hg
    simpa only [d5847, d3257, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28847 (p : Pattern) (guard : d5854 p = 1) : d3257 p ≤ (0 : Int) + d2551 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28846 p hg
    simpa only [d5854, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26655 p hg
    simpa only [d5854, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28848 (p : Pattern) (guard : d5855 p = 1) : d3257 p ≤ (0 : Int) + d2551 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28802 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28847 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28849 (p : Pattern) (guard : d5855 p = 1) : d3257 p ≤ (0 : Int) + d2583 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28848 p hg
    simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28804 p hg
    simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28850 (p : Pattern) (guard : d5855 p = 1) : d3283 p ≤ (0 : Int) + d2584 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3283, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28849 p hg
    simpa only [d3283, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3283, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28805 p hg
    simpa only [d3283, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28851 (p : Pattern) (guard : d5855 p = 1) : d3284 p ≤ (0 : Int) + d2585 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3284, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28850 p hg
    simpa only [d3284, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3284, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3284, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28852 (p : Pattern) (guard : d5855 p = 1) : d3285 p ≤ (0 : Int) + d2586 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3285, d2586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28845 p hg
    simpa only [d3285, d2586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3285, d2586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28851 p hg
    simpa only [d3285, d2586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28853 (p : Pattern) (guard : d5855 p = 1) : d3286 p ≤ (0 : Int) + d2587 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3286, d2587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28835 p hg
    simpa only [d3286, d2587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3286, d2587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28852 p hg
    simpa only [d3286, d2587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28854 (p : Pattern) (guard : d5855 p = 1) : d3287 p ≤ (0 : Int) + d2588 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3287, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28825 p hg
    simpa only [d3287, d2588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3287, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3287, d2588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28855 (p : Pattern) (guard : d5855 p = 1) : d3288 p ≤ (0 : Int) + d2589 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3288, d2589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28800 p hg
    simpa only [d3288, d2589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3288, d2589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28854 p hg
    simpa only [d3288, d2589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28856 (p : Pattern) (guard : d5855 p = 1) : d3289 p ≤ (0 : Int) + d2590 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3289, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28807 p hg
    simpa only [d3289, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3289, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28812 p hg
    simpa only [d3289, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28857 (p : Pattern) (guard : d5855 p = 1) : d3290 p ≤ (0 : Int) + d2591 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3290, d2591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28855 p hg
    simpa only [d3290, d2591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3290, d2591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28856 p hg
    simpa only [d3290, d2591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28858 (p : Pattern) (guard : d5855 p = 1) : d3291 p ≤ (0 : Int) + d2592 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3291, d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28842 p hg
    simpa only [d3291, d2592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3291, d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3291, d2592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28859 (p : Pattern) (guard : d5855 p = 1) : d3292 p ≤ (0 : Int) + d2593 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3292, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28807 p hg
    simpa only [d3292, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3292, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28858 p hg
    simpa only [d3292, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28860 (p : Pattern) (guard : d5855 p = 1) : d3293 p ≤ (0 : Int) + d2594 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3293, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28849 p hg
    simpa only [d3293, d2594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3293, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3293, d2594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28861 (p : Pattern) (guard : d5855 p = 1) : d3294 p ≤ (0 : Int) + d2595 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3294, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28860 p hg
    simpa only [d3294, d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3294, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3294, d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28862 (p : Pattern) (guard : d5855 p = 1) : d3295 p ≤ (0 : Int) + d2596 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3295, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28859 p hg
    simpa only [d3295, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3295, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28861 p hg
    simpa only [d3295, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28863 (p : Pattern) (guard : d5855 p = 1) : d3296 p ≤ (0 : Int) + d2597 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3296, d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28857 p hg
    simpa only [d3296, d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3296, d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28862 p hg
    simpa only [d3296, d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28864 (p : Pattern) (guard : d5855 p = 1) : d3297 p ≤ (0 : Int) + d2598 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3297, d2598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28853 p hg
    simpa only [d3297, d2598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3297, d2598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28863 p hg
    simpa only [d3297, d2598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28865 (p : Pattern) (guard : d5855 p = 1) : d3298 p ≤ (0 : Int) + d2599 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3298, d2599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28816 p hg
    simpa only [d3298, d2599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3298, d2599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28864 p hg
    simpa only [d3298, d2599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28866 (p : Pattern) (guard : d5855 p = 1) : d3230 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3230, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28731 p hg
    simpa only [d3230, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3230, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3230, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28867 (p : Pattern) (guard : d5855 p = 1) : d3238 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3238, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28747 p hg
    simpa only [d3238, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3238, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28866 p hg
    simpa only [d3238, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28868 (p : Pattern) (guard : d5855 p = 1) : d3240 p ≤ (0 : Int) + d2602 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3240, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28757 p hg
    simpa only [d3240, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3240, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3240, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28869 (p : Pattern) (guard : d5855 p = 1) : d3241 p ≤ (0 : Int) + d2603 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3241, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28758 p hg
    simpa only [d3241, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3241, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28868 p hg
    simpa only [d3241, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28870 (p : Pattern) (guard : d5855 p = 1) : d3242 p ≤ (0 : Int) + d2604 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3242, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28867 p hg
    simpa only [d3242, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3242, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28869 p hg
    simpa only [d3242, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28871 (p : Pattern) (guard : d5855 p = 1) : d3299 p ≤ (0 : Int) + d2605 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3299, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28867 p hg
    simpa only [d3299, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3299, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28870 p hg
    simpa only [d3299, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28872 (p : Pattern) (guard : d5855 p = 1) : d3245 p ≤ (0 : Int) + d2606 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3245, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28773 p hg
    simpa only [d3245, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3245, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3245, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28873 (p : Pattern) (guard : d5855 p = 1) : d3246 p ≤ (0 : Int) + d2607 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3246, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28774 p hg
    simpa only [d3246, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3246, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28872 p hg
    simpa only [d3246, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28874 (p : Pattern) (guard : d5855 p = 1) : d3247 p ≤ (0 : Int) + d2608 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3247, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28873 p hg
    simpa only [d3247, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3247, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3247, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28875 (p : Pattern) (guard : d5855 p = 1) : d3248 p ≤ (0 : Int) + d2609 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3248, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28870 p hg
    simpa only [d3248, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3248, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28874 p hg
    simpa only [d3248, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28876 (p : Pattern) (guard : d5855 p = 1) : d3300 p ≤ (0 : Int) + d2610 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3300, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28871 p hg
    simpa only [d3300, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3300, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28875 p hg
    simpa only [d3300, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28877 (p : Pattern) (guard : d5855 p = 1) : d3275 p ≤ (0 : Int) + d2611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3275, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28825 p hg
    simpa only [d3275, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3275, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28791 p hg
    simpa only [d3275, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28878 (p : Pattern) (guard : d5847 p = 1) : d3253 p ≤ (0 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3253, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23535 p hg
    simpa only [d5847, d3253, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3253, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20051 p hg
    simpa only [d5847, d3253, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28879 (p : Pattern) (guard : d5854 p = 1) : d3253 p ≤ (0 : Int) + d2545 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28878 p hg
    simpa only [d5854, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26649 p hg
    simpa only [d5854, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28880 (p : Pattern) (guard : d5855 p = 1) : d3253 p ≤ (0 : Int) + d2545 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28793 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28879 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28881 (p : Pattern) (guard : d5855 p = 1) : d3253 p ≤ (0 : Int) + d2612 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28880 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28798 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28882 (p : Pattern) (guard : d5855 p = 1) : d3301 p ≤ (0 : Int) + d2613 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3301, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28881 p hg
    simpa only [d3301, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3301, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28799 p hg
    simpa only [d3301, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28883 (p : Pattern) (guard : d5855 p = 1) : d3302 p ≤ (0 : Int) + d2614 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3302, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28877 p hg
    simpa only [d3302, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3302, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28882 p hg
    simpa only [d3302, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28884 (p : Pattern) (guard : d5855 p = 1) : d3303 p ≤ (0 : Int) + d2615 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3303, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28883 p hg
    simpa only [d3303, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3303, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28851 p hg
    simpa only [d3303, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28885 (p : Pattern) (guard : d5855 p = 1) : d3304 p ≤ (0 : Int) + d2616 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3304, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28884 p hg
    simpa only [d3304, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3304, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3304, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28886 (p : Pattern) (guard : d5855 p = 1) : d3305 p ≤ (0 : Int) + d2617 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3305, d2617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28876 p hg
    simpa only [d3305, d2617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3305, d2617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28885 p hg
    simpa only [d3305, d2617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28887 (p : Pattern) (guard : d5855 p = 1) : d3306 p ≤ (0 : Int) + d2618 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3306, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28867 p hg
    simpa only [d3306, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3306, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28877 p hg
    simpa only [d3306, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28888 (p : Pattern) (guard : d5855 p = 1) : d3277 p ≤ (0 : Int) + d2619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3277, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28869 p hg
    simpa only [d3277, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3277, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28873 p hg
    simpa only [d3277, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28889 (p : Pattern) (guard : d5855 p = 1) : d3307 p ≤ (0 : Int) + d2620 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3307, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28887 p hg
    simpa only [d3307, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3307, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28888 p hg
    simpa only [d3307, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28890 (p : Pattern) (guard : d5855 p = 1) : d3282 p ≤ (0 : Int) + d2621 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3282, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28869 p hg
    simpa only [d3282, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3282, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28844 p hg
    simpa only [d3282, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28891 (p : Pattern) (guard : d5855 p = 1) : d3285 p ≤ (0 : Int) + d2622 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3285, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28890 p hg
    simpa only [d3285, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3285, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28851 p hg
    simpa only [d3285, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28892 (p : Pattern) (guard : d5855 p = 1) : d3308 p ≤ (0 : Int) + d2623 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3308, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28889 p hg
    simpa only [d3308, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3308, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28891 p hg
    simpa only [d3308, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28893 (p : Pattern) (guard : d5855 p = 1) : d3309 p ≤ (0 : Int) + d2624 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3309, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28882 p hg
    simpa only [d3309, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3309, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3309, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28894 (p : Pattern) (guard : d5855 p = 1) : d3310 p ≤ (0 : Int) + d2625 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3310, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d3310, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3310, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3310, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28895 (p : Pattern) (guard : d5855 p = 1) : d3311 p ≤ (0 : Int) + d2626 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3311, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d3311, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3311, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3311, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28896 (p : Pattern) (guard : d5855 p = 1) : d3312 p ≤ (0 : Int) + d2627 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3312, d2627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28892 p hg
    simpa only [d3312, d2627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3312, d2627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d3312, d2627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28897 (p : Pattern) (guard : d5855 p = 1) : d3313 p ≤ (0 : Int) + d2628 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3313, d2628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28886 p hg
    simpa only [d3313, d2628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3313, d2628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28896 p hg
    simpa only [d3313, d2628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28898 (p : Pattern) (guard : d5855 p = 1) : d3314 p ≤ (0 : Int) + d2629 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3314, d2629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28865 p hg
    simpa only [d3314, d2629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3314, d2629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d3314, d2629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28899 (p : Pattern) (guard : d5855 p = 1) : d3315 p ≤ (0 : Int) + d2630 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3315, d2630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28873 p hg
    simpa only [d3315, d2630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3315, d2630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28850 p hg
    simpa only [d3315, d2630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28900 (p : Pattern) (guard : d5855 p = 1) : d3316 p ≤ (0 : Int) + d2631 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3316, d2631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d3316, d2631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3316, d2631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28851 p hg
    simpa only [d3316, d2631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28901 (p : Pattern) (guard : d5855 p = 1) : d3317 p ≤ (0 : Int) + d2632 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3317, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28851 p hg
    simpa only [d3317, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3317, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3317, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28902 (p : Pattern) (guard : d5855 p = 1) : d3318 p ≤ (0 : Int) + d2633 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3318, d2633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28900 p hg
    simpa only [d3318, d2633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3318, d2633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28901 p hg
    simpa only [d3318, d2633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28903 (p : Pattern) (guard : d5855 p = 1) : d3319 p ≤ (0 : Int) + d2634 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3319, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28901 p hg
    simpa only [d3319, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3319, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3319, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28904 (p : Pattern) (guard : d5855 p = 1) : d3320 p ≤ (0 : Int) + d2635 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3320, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28902 p hg
    simpa only [d3320, d2635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3320, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28903 p hg
    simpa only [d3320, d2635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28905 (p : Pattern) (guard : d5855 p = 1) : d3321 p ≤ (0 : Int) + d2636 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3321, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28903 p hg
    simpa only [d3321, d2636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3321, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3321, d2636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28906 (p : Pattern) (guard : d5855 p = 1) : d3322 p ≤ (0 : Int) + d2637 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3322, d2637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28904 p hg
    simpa only [d3322, d2637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3322, d2637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28905 p hg
    simpa only [d3322, d2637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28907 (p : Pattern) (guard : d5855 p = 1) : d3323 p ≤ (0 : Int) + d2638 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3323, d2638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d3323, d2638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3323, d2638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28906 p hg
    simpa only [d3323, d2638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28908 (p : Pattern) (guard : d5855 p = 1) : d3324 p ≤ (0 : Int) + d2639 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3324, d2639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28898 p hg
    simpa only [d3324, d2639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3324, d2639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28907 p hg
    simpa only [d3324, d2639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28909 (p : Pattern) (guard : d5855 p = 1) : d3325 p ≤ (0 : Int) + d2640 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3325, d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28744 p hg
    simpa only [d3325, d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3325, d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28748 p hg
    simpa only [d3325, d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28910 (p : Pattern) (guard : d5855 p = 1) : d3326 p ≤ (0 : Int) + d2641 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3326, d2641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28909 p hg
    simpa only [d3326, d2641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3326, d2641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28766 p hg
    simpa only [d3326, d2641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28911 (p : Pattern) (guard : d5855 p = 1) : d3327 p ≤ (0 : Int) + d2642 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3327, d2642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28910 p hg
    simpa only [d3327, d2642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3327, d2642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28783 p hg
    simpa only [d3327, d2642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28912 (p : Pattern) (guard : d5855 p = 1) : d3328 p ≤ (0 : Int) + d2643 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3328, d2643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28911 p hg
    simpa only [d3328, d2643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3328, d2643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28815 p hg
    simpa only [d3328, d2643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28913 (p : Pattern) (guard : d5855 p = 1) : d3306 p ≤ (0 : Int) + d2644 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3306, d2644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28748 p hg
    simpa only [d3306, d2644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3306, d2644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28832 p hg
    simpa only [d3306, d2644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28914 (p : Pattern) (guard : d5855 p = 1) : d3307 p ≤ (0 : Int) + d2645 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3307, d2645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28913 p hg
    simpa only [d3307, d2645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3307, d2645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28834 p hg
    simpa only [d3307, d2645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28915 (p : Pattern) (guard : d5855 p = 1) : d3308 p ≤ (0 : Int) + d2646 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3308, d2646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28914 p hg
    simpa only [d3308, d2646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3308, d2646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28852 p hg
    simpa only [d3308, d2646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28916 (p : Pattern) (guard : d5855 p = 1) : d3329 p ≤ (0 : Int) + d2647 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3329, d2647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28915 p hg
    simpa only [d3329, d2647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3329, d2647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28863 p hg
    simpa only [d3329, d2647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28917 (p : Pattern) (guard : d5855 p = 1) : d3330 p ≤ (0 : Int) + d2648 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3330, d2648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28912 p hg
    simpa only [d3330, d2648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3330, d2648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28916 p hg
    simpa only [d3330, d2648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28918 (p : Pattern) (guard : d5855 p = 1) : d3331 p ≤ (0 : Int) + d2649 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3331, d2649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28917 p hg
    simpa only [d3331, d2649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3331, d2649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d3331, d2649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28919 (p : Pattern) (guard : d5855 p = 1) : d3332 p ≤ (0 : Int) + d2650 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3332, d2650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d3332, d2650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3332, d2650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3332, d2650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28920 (p : Pattern) (guard : d5855 p = 1) : d3333 p ≤ (0 : Int) + d2651 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3333, d2651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28918 p hg
    simpa only [d3333, d2651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3333, d2651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28919 p hg
    simpa only [d3333, d2651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28921 (p : Pattern) (guard : d5855 p = 1) : d3334 p ≤ (0 : Int) + d2652 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3334, d2652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28908 p hg
    simpa only [d3334, d2652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3334, d2652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28920 p hg
    simpa only [d3334, d2652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28922 (p : Pattern) (guard : d0 p = 1) : d3226 p ≤ (0 : Int) + d356 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28923 (p : Pattern) (guard : d5851 p = 1) : d3336 p ≤ (0 : Int) + d2653 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d3336, d2653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26744 p hg
    simpa only [d5851, d3336, d2653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d3336, d2653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28922 p hg
    simpa only [d5851, d3336, d2653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28924 (p : Pattern) (guard : d5855 p = 1) : d3337 p ≤ (0 : Int) + d2654 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d3337, d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28923 p hg
    simpa only [d5855, d3337, d2654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d3337, d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28724 p hg
    simpa only [d5855, d3337, d2654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28925 (p : Pattern) (guard : d5855 p = 1) : d3338 p ≤ (0 : Int) + d2655 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3338, d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28924 p hg
    simpa only [d3338, d2655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3338, d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28731 p hg
    simpa only [d3338, d2655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28926 (p : Pattern) (guard : d5855 p = 1) : d3339 p ≤ (0 : Int) + d2656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3339, d2656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28925 p hg
    simpa only [d3339, d2656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3339, d2656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28738 p hg
    simpa only [d3339, d2656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28927 (p : Pattern) (guard : d5855 p = 1) : d3340 p ≤ (0 : Int) + d2657 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3340, d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28926 p hg
    simpa only [d3340, d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3340, d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28748 p hg
    simpa only [d3340, d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28928 (p : Pattern) (guard : d5855 p = 1) : d3341 p ≤ (0 : Int) + d2658 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3341, d2658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28927 p hg
    simpa only [d3341, d2658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3341, d2658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28766 p hg
    simpa only [d3341, d2658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28929 (p : Pattern) (guard : d5855 p = 1) : d3342 p ≤ (0 : Int) + d2659 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3342, d2659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d3342, d2659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3342, d2659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28783 p hg
    simpa only [d3342, d2659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28930 (p : Pattern) (guard : d5855 p = 1) : d3343 p ≤ (0 : Int) + d2660 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3343, d2660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28929 p hg
    simpa only [d3343, d2660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3343, d2660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28815 p hg
    simpa only [d3343, d2660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28931 (p : Pattern) (guard : d5855 p = 1) : d3344 p ≤ (0 : Int) + d2661 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3344, d2661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28744 p hg
    simpa only [d3344, d2661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3344, d2661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28832 p hg
    simpa only [d3344, d2661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28932 (p : Pattern) (guard : d5855 p = 1) : d3345 p ≤ (0 : Int) + d2662 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3345, d2662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28931 p hg
    simpa only [d3345, d2662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3345, d2662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28834 p hg
    simpa only [d3345, d2662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28933 (p : Pattern) (guard : d5855 p = 1) : d3346 p ≤ (0 : Int) + d2663 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3346, d2663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28932 p hg
    simpa only [d3346, d2663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3346, d2663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28852 p hg
    simpa only [d3346, d2663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28934 (p : Pattern) (guard : d5855 p = 1) : d3347 p ≤ (0 : Int) + d2664 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3347, d2664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28933 p hg
    simpa only [d3347, d2664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3347, d2664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28863 p hg
    simpa only [d3347, d2664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28935 (p : Pattern) (guard : d5855 p = 1) : d3348 p ≤ (0 : Int) + d2665 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3348, d2665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28930 p hg
    simpa only [d3348, d2665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3348, d2665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28934 p hg
    simpa only [d3348, d2665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28936 (p : Pattern) (guard : d5855 p = 1) : d3349 p ≤ (0 : Int) + d2666 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3349, d2666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28935 p hg
    simpa only [d3349, d2666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3349, d2666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d3349, d2666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28937 (p : Pattern) (guard : d5855 p = 1) : d3350 p ≤ (0 : Int) + d2667 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3350, d2667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28936 p hg
    simpa only [d3350, d2667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3350, d2667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28907 p hg
    simpa only [d3350, d2667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28938 (p : Pattern) (guard : d5855 p = 1) : d3299 p ≤ (0 : Int) + d2668 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3299, d2668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28748 p hg
    simpa only [d3299, d2668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3299, d2668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28766 p hg
    simpa only [d3299, d2668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28939 (p : Pattern) (guard : d5855 p = 1) : d3300 p ≤ (0 : Int) + d2669 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3300, d2669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28938 p hg
    simpa only [d3300, d2669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3300, d2669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28783 p hg
    simpa only [d3300, d2669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28940 (p : Pattern) (guard : d5855 p = 1) : d3351 p ≤ (0 : Int) + d2670 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3351, d2670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28939 p hg
    simpa only [d3351, d2670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3351, d2670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28815 p hg
    simpa only [d3351, d2670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28941 (p : Pattern) (guard : d5855 p = 1) : d3352 p ≤ (0 : Int) + d2671 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3352, d2671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28940 p hg
    simpa only [d3352, d2671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3352, d2671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28916 p hg
    simpa only [d3352, d2671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28942 (p : Pattern) (guard : d5855 p = 1) : d3353 p ≤ (0 : Int) + d2672 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3353, d2672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28941 p hg
    simpa only [d3353, d2672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3353, d2672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d3353, d2672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28943 (p : Pattern) (guard : d5855 p = 1) : d3354 p ≤ (0 : Int) + d2673 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3354, d2673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28942 p hg
    simpa only [d3354, d2673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3354, d2673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28919 p hg
    simpa only [d3354, d2673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28944 (p : Pattern) (guard : d5855 p = 1) : d3355 p ≤ (0 : Int) + d2674 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3355, d2674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28937 p hg
    simpa only [d3355, d2674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3355, d2674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28943 p hg
    simpa only [d3355, d2674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28945 (p : Pattern) (guard : d5855 p = 1) : d3356 p ≤ (0 : Int) + d2675 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3356, d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28921 p hg
    simpa only [d3356, d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3356, d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28944 p hg
    simpa only [d3356, d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28946 (p : Pattern) (guard : d0 p = 1) : d3358 p ≤ (0 : Int) + d356 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28947 (p : Pattern) (guard : d5851 p = 1) : d3359 p ≤ (0 : Int) + d2676 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d3359, d2676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26769 p hg
    simpa only [d5851, d3359, d2676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d3359, d2676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28946 p hg
    simpa only [d5851, d3359, d2676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28948 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23606 p hg
    simpa only [d5847, d3358, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20160 p hg
    simpa only [d5847, d3358, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28949 (p : Pattern) (guard : d5854 p = 1) : d3358 p ≤ (0 : Int) + d2677 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28948 p hg
    simpa only [d5854, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d5854, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28950 (p : Pattern) (guard : d5855 p = 1) : d3360 p ≤ (0 : Int) + d2678 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d3360, d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28947 p hg
    simpa only [d5855, d3360, d2678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d3360, d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28949 p hg
    simpa only [d5855, d3360, d2678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28951 (p : Pattern) (guard : d5851 p = 1) : d3358 p ≤ (0 : Int) + d2677 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26770 p hg
    simpa only [d5851, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d5851, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28952 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28953 (p : Pattern) (guard : d5843 p = 1) : d1 p ≤ (0 : Int) + d1939 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28952 p hg
    simpa only [d5843, d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28954 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d1940 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28953 p hg
    simpa only [d5847, d3358, d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20170 p hg
    simpa only [d5847, d3358, d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28955 (p : Pattern) (guard : d5854 p = 1) : d3358 p ≤ (0 : Int) + d2679 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28954 p hg
    simpa only [d5854, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d5854, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28956 (p : Pattern) (guard : d5855 p = 1) : d3358 p ≤ (0 : Int) + d2680 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28951 p hg
    simpa only [d5855, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28955 p hg
    simpa only [d5855, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28957 (p : Pattern) (guard : d5855 p = 1) : d3361 p ≤ (0 : Int) + d2681 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3361, d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28950 p hg
    simpa only [d3361, d2681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3361, d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d3361, d2681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28958 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28959 (p : Pattern) (guard : d5843 p = 1) : d1 p ≤ (0 : Int) + d1872 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28958 p hg
    simpa only [d5843, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28960 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d1873 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28959 p hg
    simpa only [d5847, d3358, d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20238 p hg
    simpa only [d5847, d3358, d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28961 (p : Pattern) (guard : d5854 p = 1) : d3358 p ≤ (0 : Int) + d2682 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28960 p hg
    simpa only [d5854, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d5854, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28962 (p : Pattern) (guard : d5855 p = 1) : d3358 p ≤ (0 : Int) + d2683 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28951 p hg
    simpa only [d5855, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28961 p hg
    simpa only [d5855, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28963 (p : Pattern) (guard : d5855 p = 1) : d3362 p ≤ (0 : Int) + d2684 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3362, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d3362, d2684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3362, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3362, d2684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28964 (p : Pattern) (guard : d5855 p = 1) : d3363 p ≤ (0 : Int) + d2685 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3363, d2685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d3363, d2685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3363, d2685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28963 p hg
    simpa only [d3363, d2685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28965 (p : Pattern) (guard : d5855 p = 1) : d3358 p ≤ (0 : Int) + d2677 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28951 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28949 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28966 (p : Pattern) (guard : d5855 p = 1) : d3358 p ≤ (0 : Int) + d2686 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28965 p hg
    simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28967 (p : Pattern) (guard : d5855 p = 1) : d3364 p ≤ (0 : Int) + d2687 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3364, d2687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28966 p hg
    simpa only [d3364, d2687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3364, d2687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28963 p hg
    simpa only [d3364, d2687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28968 (p : Pattern) (guard : d5855 p = 1) : d3365 p ≤ (0 : Int) + d2688 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3365, d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28964 p hg
    simpa only [d3365, d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3365, d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28967 p hg
    simpa only [d3365, d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28969 (p : Pattern) (guard : d5851 p = 1) : d3366 p ≤ (0 : Int) + d2689 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26785 p hg
    simpa only [d5851, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d5851, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28970 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3366, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23629 p hg
    simpa only [d5847, d3366, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3366, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20170 p hg
    simpa only [d5847, d3366, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28971 (p : Pattern) (guard : d5854 p = 1) : d3366 p ≤ (0 : Int) + d2689 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28970 p hg
    simpa only [d5854, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d5854, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28972 (p : Pattern) (guard : d5855 p = 1) : d3366 p ≤ (0 : Int) + d2689 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28969 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28971 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28973 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28974 (p : Pattern) (guard : d5843 p = 1) : d5 p ≤ (0 : Int) + d1963 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14654 p hg
    simpa only [d5843, d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28973 p hg
    simpa only [d5843, d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28975 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d1964 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3366, d1964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28974 p hg
    simpa only [d5847, d3366, d1964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3366, d1964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19893 p hg
    simpa only [d5847, d3366, d1964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28976 (p : Pattern) (guard : d5854 p = 1) : d3366 p ≤ (0 : Int) + d2690 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28975 p hg
    simpa only [d5854, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d5854, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28977 (p : Pattern) (guard : d5855 p = 1) : d3366 p ≤ (0 : Int) + d2691 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28969 p hg
    simpa only [d5855, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28976 p hg
    simpa only [d5855, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28978 (p : Pattern) (guard : d5855 p = 1) : d3366 p ≤ (0 : Int) + d2692 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28972 p hg
    simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28977 p hg
    simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28979 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
