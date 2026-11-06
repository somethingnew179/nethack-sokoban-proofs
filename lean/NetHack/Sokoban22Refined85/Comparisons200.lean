/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons199
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare28000 (p : Pattern) (guard : d6558 p = 1) : d3289 p ≤ (0 : Int) + d6655 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3289, d6655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27956 p hg
    simpa only [d3289, d6655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3289, d6655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27961 p hg
    simpa only [d3289, d6655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28001 (p : Pattern) (guard : d6558 p = 1) : d3290 p ≤ (0 : Int) + d6656 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3290, d6656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27999 p hg
    simpa only [d3290, d6656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3290, d6656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28000 p hg
    simpa only [d3290, d6656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28002 (p : Pattern) (guard : d6558 p = 1) : d3291 p ≤ (0 : Int) + d6657 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3291, d6657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27988 p hg
    simpa only [d3291, d6657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3291, d6657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3291, d6657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28003 (p : Pattern) (guard : d6558 p = 1) : d3292 p ≤ (0 : Int) + d6658 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3292, d6658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27956 p hg
    simpa only [d3292, d6658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3292, d6658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28002 p hg
    simpa only [d3292, d6658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28004 (p : Pattern) (guard : d6558 p = 1) : d3293 p ≤ (0 : Int) + d6659 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3293, d6659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27992 p hg
    simpa only [d3293, d6659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3293, d6659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3293, d6659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28005 (p : Pattern) (guard : d6558 p = 1) : d3294 p ≤ (0 : Int) + d6660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3294, d6660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28004 p hg
    simpa only [d3294, d6660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3294, d6660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3294, d6660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28006 (p : Pattern) (guard : d6558 p = 1) : d3295 p ≤ (0 : Int) + d6661 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3295, d6661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28003 p hg
    simpa only [d3295, d6661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3295, d6661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28005 p hg
    simpa only [d3295, d6661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28007 (p : Pattern) (guard : d6558 p = 1) : d3296 p ≤ (0 : Int) + d6662 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3296, d6662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28001 p hg
    simpa only [d3296, d6662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3296, d6662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28006 p hg
    simpa only [d3296, d6662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28008 (p : Pattern) (guard : d6558 p = 1) : d3297 p ≤ (0 : Int) + d6663 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3297, d6663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27996 p hg
    simpa only [d3297, d6663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3297, d6663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28007 p hg
    simpa only [d3297, d6663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28009 (p : Pattern) (guard : d6558 p = 1) : d3298 p ≤ (0 : Int) + d6664 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3298, d6664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27965 p hg
    simpa only [d3298, d6664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3298, d6664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28008 p hg
    simpa only [d3298, d6664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28010 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6665 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27871 p hg
    simpa only [d6665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27917 p hg
    simpa only [d6665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28011 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6666 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27918 p hg
    simpa only [d6666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28010 p hg
    simpa only [d6666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28012 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6667 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27868 p hg
    simpa only [d6667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28011 p hg
    simpa only [d6667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28013 (p : Pattern) (guard : d6558 p = 1) : d3230 p ≤ (0 : Int) + d6668 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3230, d6668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27873 p hg
    simpa only [d3230, d6668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3230, d6668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3230, d6668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28014 (p : Pattern) (guard : d6558 p = 1) : d3238 p ≤ (0 : Int) + d6669 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3238, d6669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28012 p hg
    simpa only [d3238, d6669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3238, d6669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28013 p hg
    simpa only [d3238, d6669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28015 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6670 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3226, d6670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27865 p hg
    simpa only [d6558, d3226, d6670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3226, d6670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23784 p hg
    simpa only [d6558, d3226, d6670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28016 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6671 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27871 p hg
    simpa only [d6671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28015 p hg
    simpa only [d6671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28017 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6672 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27918 p hg
    simpa only [d6672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28016 p hg
    simpa only [d6672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28018 (p : Pattern) (guard : d6558 p = 1) : d3230 p ≤ (0 : Int) + d6673 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3230, d6673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28017 p hg
    simpa only [d3230, d6673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3230, d6673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3230, d6673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28019 (p : Pattern) (guard : d6558 p = 1) : d3238 p ≤ (0 : Int) + d6674 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3238, d6674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27922 p hg
    simpa only [d3238, d6674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3238, d6674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28018 p hg
    simpa only [d3238, d6674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28020 (p : Pattern) (guard : d6558 p = 1) : d3238 p ≤ (0 : Int) + d6675 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28014 p hg
    simpa only [d6675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28019 p hg
    simpa only [d6675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28021 (p : Pattern) (guard : d6558 p = 1) : d3230 p ≤ (0 : Int) + d6676 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3230, d6676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27921 p hg
    simpa only [d3230, d6676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3230, d6676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3230, d6676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28022 (p : Pattern) (guard : d6558 p = 1) : d3238 p ≤ (0 : Int) + d6677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3238, d6677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27922 p hg
    simpa only [d3238, d6677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3238, d6677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28021 p hg
    simpa only [d3238, d6677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28023 (p : Pattern) (guard : d6558 p = 1) : d3240 p ≤ (0 : Int) + d6678 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3240, d6678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27954 p hg
    simpa only [d3240, d6678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3240, d6678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3240, d6678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28024 (p : Pattern) (guard : d6558 p = 1) : d3241 p ≤ (0 : Int) + d6679 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3241, d6679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27955 p hg
    simpa only [d3241, d6679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3241, d6679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28023 p hg
    simpa only [d3241, d6679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28025 (p : Pattern) (guard : d6558 p = 1) : d3242 p ≤ (0 : Int) + d6680 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3242, d6680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28022 p hg
    simpa only [d3242, d6680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3242, d6680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28024 p hg
    simpa only [d3242, d6680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28026 (p : Pattern) (guard : d6558 p = 1) : d3299 p ≤ (0 : Int) + d6681 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3299, d6681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28020 p hg
    simpa only [d3299, d6681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3299, d6681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28025 p hg
    simpa only [d3299, d6681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28027 (p : Pattern) (guard : d6558 p = 1) : d3245 p ≤ (0 : Int) + d6682 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3245, d6682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27907 p hg
    simpa only [d3245, d6682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3245, d6682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3245, d6682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28028 (p : Pattern) (guard : d6558 p = 1) : d3246 p ≤ (0 : Int) + d6683 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3246, d6683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27908 p hg
    simpa only [d3246, d6683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3246, d6683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28027 p hg
    simpa only [d3246, d6683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28029 (p : Pattern) (guard : d6558 p = 1) : d3247 p ≤ (0 : Int) + d6684 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3247, d6684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28028 p hg
    simpa only [d3247, d6684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3247, d6684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3247, d6684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28030 (p : Pattern) (guard : d6558 p = 1) : d3248 p ≤ (0 : Int) + d6685 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3248, d6685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28025 p hg
    simpa only [d3248, d6685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3248, d6685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28029 p hg
    simpa only [d3248, d6685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28031 (p : Pattern) (guard : d6558 p = 1) : d3300 p ≤ (0 : Int) + d6686 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3300, d6686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28026 p hg
    simpa only [d3300, d6686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3300, d6686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28030 p hg
    simpa only [d3300, d6686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28032 (p : Pattern) (guard : d6558 p = 1) : d3275 p ≤ (0 : Int) + d6687 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3275, d6687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27997 p hg
    simpa only [d3275, d6687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3275, d6687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27931 p hg
    simpa only [d3275, d6687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28033 (p : Pattern) (guard : d6558 p = 1) : d3253 p ≤ (0 : Int) + d6688 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27934 p hg
    simpa only [d6688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27939 p hg
    simpa only [d6688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28034 (p : Pattern) (guard : d6558 p = 1) : d3301 p ≤ (0 : Int) + d6689 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3301, d6689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28033 p hg
    simpa only [d3301, d6689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3301, d6689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27940 p hg
    simpa only [d3301, d6689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28035 (p : Pattern) (guard : d6558 p = 1) : d3302 p ≤ (0 : Int) + d6690 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3302, d6690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28032 p hg
    simpa only [d3302, d6690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3302, d6690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28034 p hg
    simpa only [d3302, d6690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28036 (p : Pattern) (guard : d6558 p = 1) : d3303 p ≤ (0 : Int) + d6691 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3303, d6691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28035 p hg
    simpa only [d3303, d6691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3303, d6691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27994 p hg
    simpa only [d3303, d6691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28037 (p : Pattern) (guard : d6558 p = 1) : d3304 p ≤ (0 : Int) + d6692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3304, d6692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28036 p hg
    simpa only [d3304, d6692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3304, d6692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3304, d6692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28038 (p : Pattern) (guard : d6558 p = 1) : d3305 p ≤ (0 : Int) + d6693 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3305, d6693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28031 p hg
    simpa only [d3305, d6693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3305, d6693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28037 p hg
    simpa only [d3305, d6693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28039 (p : Pattern) (guard : d6558 p = 1) : d3306 p ≤ (0 : Int) + d6694 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3306, d6694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28019 p hg
    simpa only [d3306, d6694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3306, d6694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28032 p hg
    simpa only [d3306, d6694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28040 (p : Pattern) (guard : d6558 p = 1) : d3277 p ≤ (0 : Int) + d6695 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3277, d6695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28024 p hg
    simpa only [d3277, d6695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3277, d6695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28028 p hg
    simpa only [d3277, d6695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28041 (p : Pattern) (guard : d6558 p = 1) : d3307 p ≤ (0 : Int) + d6696 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3307, d6696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28039 p hg
    simpa only [d3307, d6696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3307, d6696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28040 p hg
    simpa only [d3307, d6696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28042 (p : Pattern) (guard : d6558 p = 1) : d3282 p ≤ (0 : Int) + d6697 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3282, d6697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28024 p hg
    simpa only [d3282, d6697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3282, d6697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27990 p hg
    simpa only [d3282, d6697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28043 (p : Pattern) (guard : d6558 p = 1) : d3285 p ≤ (0 : Int) + d6698 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3285, d6698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28042 p hg
    simpa only [d3285, d6698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3285, d6698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27994 p hg
    simpa only [d3285, d6698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28044 (p : Pattern) (guard : d6558 p = 1) : d3308 p ≤ (0 : Int) + d6699 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3308, d6699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28041 p hg
    simpa only [d3308, d6699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3308, d6699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28043 p hg
    simpa only [d3308, d6699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28045 (p : Pattern) (guard : d6558 p = 1) : d3309 p ≤ (0 : Int) + d6700 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3309, d6700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28034 p hg
    simpa only [d3309, d6700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3309, d6700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3309, d6700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28046 (p : Pattern) (guard : d6558 p = 1) : d3310 p ≤ (0 : Int) + d6701 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3310, d6701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28045 p hg
    simpa only [d3310, d6701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3310, d6701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3310, d6701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28047 (p : Pattern) (guard : d6558 p = 1) : d3311 p ≤ (0 : Int) + d6702 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3311, d6702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28046 p hg
    simpa only [d3311, d6702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3311, d6702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3311, d6702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28048 (p : Pattern) (guard : d6558 p = 1) : d3312 p ≤ (0 : Int) + d6703 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3312, d6703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28044 p hg
    simpa only [d3312, d6703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3312, d6703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28047 p hg
    simpa only [d3312, d6703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28049 (p : Pattern) (guard : d6558 p = 1) : d3313 p ≤ (0 : Int) + d6704 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3313, d6704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28038 p hg
    simpa only [d3313, d6704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3313, d6704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28048 p hg
    simpa only [d3313, d6704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28050 (p : Pattern) (guard : d6558 p = 1) : d3314 p ≤ (0 : Int) + d6705 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3314, d6705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28009 p hg
    simpa only [d3314, d6705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3314, d6705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28049 p hg
    simpa only [d3314, d6705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28051 (p : Pattern) (guard : d6558 p = 1) : d3315 p ≤ (0 : Int) + d6706 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3315, d6706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28028 p hg
    simpa only [d3315, d6706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3315, d6706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27993 p hg
    simpa only [d3315, d6706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28052 (p : Pattern) (guard : d6558 p = 1) : d3316 p ≤ (0 : Int) + d6707 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3316, d6707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28051 p hg
    simpa only [d3316, d6707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3316, d6707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27994 p hg
    simpa only [d3316, d6707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28053 (p : Pattern) (guard : d6558 p = 1) : d3317 p ≤ (0 : Int) + d6708 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3317, d6708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27994 p hg
    simpa only [d3317, d6708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3317, d6708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3317, d6708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28054 (p : Pattern) (guard : d6558 p = 1) : d3318 p ≤ (0 : Int) + d6709 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3318, d6709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28052 p hg
    simpa only [d3318, d6709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3318, d6709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28053 p hg
    simpa only [d3318, d6709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28055 (p : Pattern) (guard : d6558 p = 1) : d3319 p ≤ (0 : Int) + d6710 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3319, d6710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28053 p hg
    simpa only [d3319, d6710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3319, d6710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3319, d6710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28056 (p : Pattern) (guard : d6558 p = 1) : d3320 p ≤ (0 : Int) + d6711 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3320, d6711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28054 p hg
    simpa only [d3320, d6711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3320, d6711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28055 p hg
    simpa only [d3320, d6711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28057 (p : Pattern) (guard : d6558 p = 1) : d3321 p ≤ (0 : Int) + d6712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3321, d6712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28055 p hg
    simpa only [d3321, d6712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3321, d6712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3321, d6712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28058 (p : Pattern) (guard : d6558 p = 1) : d3322 p ≤ (0 : Int) + d6713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3322, d6713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28056 p hg
    simpa only [d3322, d6713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3322, d6713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28057 p hg
    simpa only [d3322, d6713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28059 (p : Pattern) (guard : d6558 p = 1) : d3323 p ≤ (0 : Int) + d6714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3323, d6714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28049 p hg
    simpa only [d3323, d6714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3323, d6714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28058 p hg
    simpa only [d3323, d6714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28060 (p : Pattern) (guard : d6558 p = 1) : d3324 p ≤ (0 : Int) + d6715 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3324, d6715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28050 p hg
    simpa only [d3324, d6715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3324, d6715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28059 p hg
    simpa only [d3324, d6715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28061 (p : Pattern) (guard : d6558 p = 1) : d3325 p ≤ (0 : Int) + d6567 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27886 p hg
    simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27889 p hg
    simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28062 (p : Pattern) (guard : d6558 p = 1) : d3326 p ≤ (0 : Int) + d6578 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3326, d6578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28061 p hg
    simpa only [d3326, d6578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3326, d6578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27901 p hg
    simpa only [d3326, d6578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28063 (p : Pattern) (guard : d6558 p = 1) : d3327 p ≤ (0 : Int) + d6589 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3327, d6589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28062 p hg
    simpa only [d3327, d6589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3327, d6589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27915 p hg
    simpa only [d3327, d6589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28064 (p : Pattern) (guard : d6558 p = 1) : d3328 p ≤ (0 : Int) + d6629 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3328, d6629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28063 p hg
    simpa only [d3328, d6629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3328, d6629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27964 p hg
    simpa only [d3328, d6629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28065 (p : Pattern) (guard : d6558 p = 1) : d3306 p ≤ (0 : Int) + d6638 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3306, d6638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27889 p hg
    simpa only [d3306, d6638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3306, d6638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27979 p hg
    simpa only [d3306, d6638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28066 (p : Pattern) (guard : d6558 p = 1) : d3307 p ≤ (0 : Int) + d6640 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3307, d6640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28065 p hg
    simpa only [d3307, d6640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3307, d6640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27981 p hg
    simpa only [d3307, d6640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28067 (p : Pattern) (guard : d6558 p = 1) : d3308 p ≤ (0 : Int) + d6651 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3308, d6651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28066 p hg
    simpa only [d3308, d6651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3308, d6651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27995 p hg
    simpa only [d3308, d6651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28068 (p : Pattern) (guard : d6558 p = 1) : d3329 p ≤ (0 : Int) + d6663 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3329, d6663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28067 p hg
    simpa only [d3329, d6663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3329, d6663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28007 p hg
    simpa only [d3329, d6663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28069 (p : Pattern) (guard : d6558 p = 1) : d3330 p ≤ (0 : Int) + d6664 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3330, d6664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28064 p hg
    simpa only [d3330, d6664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3330, d6664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28068 p hg
    simpa only [d3330, d6664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28070 (p : Pattern) (guard : d6558 p = 1) : d3331 p ≤ (0 : Int) + d6705 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3331, d6705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28069 p hg
    simpa only [d3331, d6705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3331, d6705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28049 p hg
    simpa only [d3331, d6705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28071 (p : Pattern) (guard : d6558 p = 1) : d3332 p ≤ (0 : Int) + d6716 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3332, d6716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28049 p hg
    simpa only [d3332, d6716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3332, d6716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3332, d6716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28072 (p : Pattern) (guard : d6558 p = 1) : d3333 p ≤ (0 : Int) + d6717 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3333, d6717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28070 p hg
    simpa only [d3333, d6717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3333, d6717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28071 p hg
    simpa only [d3333, d6717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28073 (p : Pattern) (guard : d6558 p = 1) : d3334 p ≤ (0 : Int) + d6718 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3334, d6718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28060 p hg
    simpa only [d3334, d6718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3334, d6718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28072 p hg
    simpa only [d3334, d6718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28074 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28075 (p : Pattern) (guard : d6558 p = 1) : d3335 p ≤ (0 : Int) + d0 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27865 p hg
    simpa only [d6558, d3335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28074 p hg
    simpa only [d6558, d3335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28076 (p : Pattern) (guard : d6558 p = 1) : d3336 p ≤ (0 : Int) + d0 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28075 p hg
    simpa only [d3336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27868 p hg
    simpa only [d3336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28077 (p : Pattern) (guard : d6558 p = 1) : d3337 p ≤ (0 : Int) + d0 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28076 p hg
    simpa only [d3337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27868 p hg
    simpa only [d3337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28078 (p : Pattern) (guard : d6558 p = 1) : d3338 p ≤ (0 : Int) + d6562 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3338, d6562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28077 p hg
    simpa only [d3338, d6562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3338, d6562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27873 p hg
    simpa only [d3338, d6562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28079 (p : Pattern) (guard : d6558 p = 1) : d3339 p ≤ (0 : Int) + d6567 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3339, d6567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28078 p hg
    simpa only [d3339, d6567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3339, d6567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27879 p hg
    simpa only [d3339, d6567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28080 (p : Pattern) (guard : d6558 p = 1) : d3340 p ≤ (0 : Int) + d6567 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28079 p hg
    simpa only [d3340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27889 p hg
    simpa only [d3340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28081 (p : Pattern) (guard : d6558 p = 1) : d3341 p ≤ (0 : Int) + d6578 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3341, d6578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28080 p hg
    simpa only [d3341, d6578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3341, d6578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27901 p hg
    simpa only [d3341, d6578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28082 (p : Pattern) (guard : d6558 p = 1) : d3342 p ≤ (0 : Int) + d6589 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3342, d6589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28081 p hg
    simpa only [d3342, d6589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3342, d6589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27915 p hg
    simpa only [d3342, d6589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28083 (p : Pattern) (guard : d6558 p = 1) : d3343 p ≤ (0 : Int) + d6629 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3343, d6629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28082 p hg
    simpa only [d3343, d6629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3343, d6629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27964 p hg
    simpa only [d3343, d6629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28084 (p : Pattern) (guard : d6558 p = 1) : d3344 p ≤ (0 : Int) + d6638 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3344, d6638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27886 p hg
    simpa only [d3344, d6638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3344, d6638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27979 p hg
    simpa only [d3344, d6638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28085 (p : Pattern) (guard : d6558 p = 1) : d3345 p ≤ (0 : Int) + d6640 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3345, d6640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28084 p hg
    simpa only [d3345, d6640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3345, d6640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27981 p hg
    simpa only [d3345, d6640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28086 (p : Pattern) (guard : d6558 p = 1) : d3346 p ≤ (0 : Int) + d6651 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3346, d6651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28085 p hg
    simpa only [d3346, d6651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3346, d6651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27995 p hg
    simpa only [d3346, d6651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28087 (p : Pattern) (guard : d6558 p = 1) : d3347 p ≤ (0 : Int) + d6663 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3347, d6663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28086 p hg
    simpa only [d3347, d6663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3347, d6663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28007 p hg
    simpa only [d3347, d6663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28088 (p : Pattern) (guard : d6558 p = 1) : d3348 p ≤ (0 : Int) + d6664 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3348, d6664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28083 p hg
    simpa only [d3348, d6664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3348, d6664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28087 p hg
    simpa only [d3348, d6664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28089 (p : Pattern) (guard : d6558 p = 1) : d3349 p ≤ (0 : Int) + d6705 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3349, d6705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28088 p hg
    simpa only [d3349, d6705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3349, d6705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28049 p hg
    simpa only [d3349, d6705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28090 (p : Pattern) (guard : d6558 p = 1) : d3350 p ≤ (0 : Int) + d6715 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3350, d6715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28089 p hg
    simpa only [d3350, d6715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3350, d6715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28059 p hg
    simpa only [d3350, d6715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28091 (p : Pattern) (guard : d6558 p = 1) : d3299 p ≤ (0 : Int) + d6578 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3299, d6578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27889 p hg
    simpa only [d3299, d6578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3299, d6578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27901 p hg
    simpa only [d3299, d6578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28092 (p : Pattern) (guard : d6558 p = 1) : d3300 p ≤ (0 : Int) + d6589 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3300, d6589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28091 p hg
    simpa only [d3300, d6589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3300, d6589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27915 p hg
    simpa only [d3300, d6589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28093 (p : Pattern) (guard : d6558 p = 1) : d3351 p ≤ (0 : Int) + d6629 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3351, d6629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28092 p hg
    simpa only [d3351, d6629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3351, d6629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27964 p hg
    simpa only [d3351, d6629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28094 (p : Pattern) (guard : d6558 p = 1) : d3352 p ≤ (0 : Int) + d6664 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3352, d6664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28093 p hg
    simpa only [d3352, d6664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3352, d6664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28068 p hg
    simpa only [d3352, d6664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28095 (p : Pattern) (guard : d6558 p = 1) : d3353 p ≤ (0 : Int) + d6705 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3353, d6705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28094 p hg
    simpa only [d3353, d6705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3353, d6705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28049 p hg
    simpa only [d3353, d6705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28096 (p : Pattern) (guard : d6558 p = 1) : d3354 p ≤ (0 : Int) + d6717 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3354, d6717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28095 p hg
    simpa only [d3354, d6717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3354, d6717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28071 p hg
    simpa only [d3354, d6717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28097 (p : Pattern) (guard : d6558 p = 1) : d3355 p ≤ (0 : Int) + d6718 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3355, d6718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28090 p hg
    simpa only [d3355, d6718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3355, d6718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28096 p hg
    simpa only [d3355, d6718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28098 (p : Pattern) (guard : d6558 p = 1) : d3356 p ≤ (0 : Int) + d6718 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28073 p hg
    simpa only [d3356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28097 p hg
    simpa only [d3356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28099 (p : Pattern) (guard : d5842 p = 1) : d1 p ≤ (0 : Int) + d1 p := by
  omega
theorem compare28100 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (0 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28101 (p : Pattern) (guard : d6558 p = 1) : d3357 p ≤ (0 : Int) + d1 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28099 p hg
    simpa only [d6558, d3357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28100 p hg
    simpa only [d6558, d3357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28102 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d1 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28099 p hg
    simpa only [d6558, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26430 p hg
    simpa only [d6558, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28103 (p : Pattern) (guard : d6558 p = 1) : d3359 p ≤ (0 : Int) + d1 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28101 p hg
    simpa only [d3359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28102 p hg
    simpa only [d3359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28104 (p : Pattern) (guard : d6558 p = 1) : d3360 p ≤ (0 : Int) + d1 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28103 p hg
    simpa only [d3360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28102 p hg
    simpa only [d3360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28105 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6719 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3358, d6719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28099 p hg
    simpa only [d6558, d3358, d6719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3358, d6719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26436 p hg
    simpa only [d6558, d3358, d6719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28106 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6720 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28102 p hg
    simpa only [d6720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28105 p hg
    simpa only [d6720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28107 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6721 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28106 p hg
    simpa only [d6721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28105 p hg
    simpa only [d6721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28108 (p : Pattern) (guard : d6558 p = 1) : d3361 p ≤ (0 : Int) + d6722 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3361, d6722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28104 p hg
    simpa only [d3361, d6722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3361, d6722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28107 p hg
    simpa only [d3361, d6722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28109 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6723 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3358, d6723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28099 p hg
    simpa only [d6558, d3358, d6723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3358, d6723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26447 p hg
    simpa only [d6558, d3358, d6723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28110 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6724 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28102 p hg
    simpa only [d6724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28109 p hg
    simpa only [d6724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28111 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6725 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28110 p hg
    simpa only [d6725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28109 p hg
    simpa only [d6725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28112 (p : Pattern) (guard : d6558 p = 1) : d3362 p ≤ (0 : Int) + d6726 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3362, d6726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28111 p hg
    simpa only [d3362, d6726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3362, d6726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3362, d6726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28113 (p : Pattern) (guard : d6558 p = 1) : d3363 p ≤ (0 : Int) + d6727 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3363, d6727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28108 p hg
    simpa only [d3363, d6727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3363, d6727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28112 p hg
    simpa only [d3363, d6727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28114 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6722 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28102 p hg
    simpa only [d6722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28107 p hg
    simpa only [d6722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28115 (p : Pattern) (guard : d6558 p = 1) : d3364 p ≤ (0 : Int) + d6727 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3364, d6727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28114 p hg
    simpa only [d3364, d6727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3364, d6727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28112 p hg
    simpa only [d3364, d6727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28116 (p : Pattern) (guard : d6558 p = 1) : d3365 p ≤ (0 : Int) + d6727 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28113 p hg
    simpa only [d3365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28115 p hg
    simpa only [d3365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28117 (p : Pattern) (guard : d5842 p = 1) : d5 p ≤ (0 : Int) + d5 p := by
  omega
theorem compare28118 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d5 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28117 p hg
    simpa only [d6558, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26436 p hg
    simpa only [d6558, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28119 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d6728 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3366, d6728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28117 p hg
    simpa only [d6558, d3366, d6728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3366, d6728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23417 p hg
    simpa only [d6558, d3366, d6728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28120 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d6729 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28118 p hg
    simpa only [d6729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28119 p hg
    simpa only [d6729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28121 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d6730 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28120 p hg
    simpa only [d6730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28119 p hg
    simpa only [d6730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28122 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d6731 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28118 p hg
    simpa only [d6731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28121 p hg
    simpa only [d6731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28123 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d6732 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3366, d6732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28117 p hg
    simpa only [d6558, d3366, d6732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3366, d6732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26453 p hg
    simpa only [d6558, d3366, d6732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28124 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d6733 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28118 p hg
    simpa only [d6733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28123 p hg
    simpa only [d6733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28125 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d6734 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28124 p hg
    simpa only [d6734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28123 p hg
    simpa only [d6734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28126 (p : Pattern) (guard : d6558 p = 1) : d3367 p ≤ (0 : Int) + d6735 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3367, d6735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28125 p hg
    simpa only [d3367, d6735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3367, d6735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3367, d6735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28127 (p : Pattern) (guard : d6558 p = 1) : d3368 p ≤ (0 : Int) + d6736 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3368, d6736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28122 p hg
    simpa only [d3368, d6736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3368, d6736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28126 p hg
    simpa only [d3368, d6736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28128 (p : Pattern) (guard : d6558 p = 1) : d3369 p ≤ (0 : Int) + d6737 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3369, d6737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28115 p hg
    simpa only [d3369, d6737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3369, d6737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28127 p hg
    simpa only [d3369, d6737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28129 (p : Pattern) (guard : d6558 p = 1) : d3370 p ≤ (0 : Int) + d6738 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3370, d6738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28116 p hg
    simpa only [d3370, d6738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3370, d6738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28128 p hg
    simpa only [d3370, d6738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28130 (p : Pattern) (guard : d6558 p = 1) : d3371 p ≤ (0 : Int) + d6739 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3371, d6739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27990 p hg
    simpa only [d3371, d6739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3371, d6739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3371, d6739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28131 (p : Pattern) (guard : d6558 p = 1) : d3372 p ≤ (0 : Int) + d6740 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3372, d6740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28128 p hg
    simpa only [d3372, d6740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3372, d6740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28130 p hg
    simpa only [d3372, d6740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28132 (p : Pattern) (guard : d6558 p = 1) : d3373 p ≤ (0 : Int) + d6741 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3373, d6741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28129 p hg
    simpa only [d3373, d6741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3373, d6741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28131 p hg
    simpa only [d3373, d6741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28133 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6742 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3358, d6742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28099 p hg
    simpa only [d6558, d3358, d6742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3358, d6742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26453 p hg
    simpa only [d6558, d3358, d6742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28134 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6743 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28102 p hg
    simpa only [d6743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28133 p hg
    simpa only [d6743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28135 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6744 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3358, d6744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28099 p hg
    simpa only [d6558, d3358, d6744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3358, d6744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23493 p hg
    simpa only [d6558, d3358, d6744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28136 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6745 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28105 p hg
    simpa only [d6745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28135 p hg
    simpa only [d6745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28137 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6746 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28134 p hg
    simpa only [d6746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28136 p hg
    simpa only [d6746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28138 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6747 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28102 p hg
    simpa only [d6747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28137 p hg
    simpa only [d6747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28139 (p : Pattern) (guard : d5842 p = 1) : d3 p ≤ (0 : Int) + d3 p := by
  omega
end NetHack.Sokoban22Refined85
