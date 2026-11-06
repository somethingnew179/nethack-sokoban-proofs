/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons168
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare23660 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23661 (p : Pattern) (guard : d5843 p = 1) : d1902 p ≤ (0 : Int) + d7 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14675 p hg
    simpa only [d5843, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23660 p hg
    simpa only [d5843, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23662 (p : Pattern) (guard : d5847 p = 1) : d1903 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1903, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23661 p hg
    simpa only [d5847, d1903, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1903, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5847, d1903, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23663 (p : Pattern) (guard : d5854 p = 1) : d2708 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23662 p hg
    simpa only [d5854, d2708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18804 p hg
    simpa only [d5854, d2708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23664 (p : Pattern) (guard : d5855 p = 1) : d2709 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23659 p hg
    simpa only [d5855, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23663 p hg
    simpa only [d5855, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23665 (p : Pattern) (guard : d5855 p = 1) : d2710 p ≤ (0 : Int) + d3378 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2710, d3378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23664 p hg
    simpa only [d2710, d3378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2710, d3378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2710, d3378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23666 (p : Pattern) (guard : d5855 p = 1) : d2711 p ≤ (0 : Int) + d3379 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2711, d3379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23625 p hg
    simpa only [d2711, d3379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2711, d3379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23665 p hg
    simpa only [d2711, d3379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23667 (p : Pattern) (guard : d5855 p = 1) : d2712 p ≤ (0 : Int) + d3380 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2712, d3380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23658 p hg
    simpa only [d2712, d3380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2712, d3380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23666 p hg
    simpa only [d2712, d3380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23668 (p : Pattern) (guard : d5855 p = 1) : d2713 p ≤ (0 : Int) + d3381 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2713, d3381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23625 p hg
    simpa only [d2713, d3381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2713, d3381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2713, d3381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23669 (p : Pattern) (guard : d5855 p = 1) : d2714 p ≤ (0 : Int) + d3382 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2714, d3382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23638 p hg
    simpa only [d2714, d3382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2714, d3382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2714, d3382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23670 (p : Pattern) (guard : d5855 p = 1) : d2715 p ≤ (0 : Int) + d3383 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2715, d3383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23668 p hg
    simpa only [d2715, d3383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2715, d3383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23669 p hg
    simpa only [d2715, d3383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23671 (p : Pattern) (guard : d5855 p = 1) : d2716 p ≤ (0 : Int) + d3384 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2716, d3384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23667 p hg
    simpa only [d2716, d3384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2716, d3384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23670 p hg
    simpa only [d2716, d3384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23672 (p : Pattern) (guard : d5855 p = 1) : d2717 p ≤ (0 : Int) + d3385 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2717, d3385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23515 p hg
    simpa only [d2717, d3385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2717, d3385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2717, d3385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23673 (p : Pattern) (guard : d5855 p = 1) : d2718 p ≤ (0 : Int) + d3386 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2718, d3386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23670 p hg
    simpa only [d2718, d3386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2718, d3386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23672 p hg
    simpa only [d2718, d3386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23674 (p : Pattern) (guard : d5855 p = 1) : d2719 p ≤ (0 : Int) + d3387 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2719, d3387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23671 p hg
    simpa only [d2719, d3387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2719, d3387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23673 p hg
    simpa only [d2719, d3387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23675 (p : Pattern) (guard : d5855 p = 1) : d2720 p ≤ (0 : Int) + d3388 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2720, d3388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23650 p hg
    simpa only [d2720, d3388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2720, d3388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23674 p hg
    simpa only [d2720, d3388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23676 (p : Pattern) (guard : d0 p = 1) : d327 p ≤ (0 : Int) + d3358 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23677 (p : Pattern) (guard : d5851 p = 1) : d2721 p ≤ (0 : Int) + d3390 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2721, d3390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17824 p hg
    simpa only [d5851, d2721, d3390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2721, d3390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23676 p hg
    simpa only [d5851, d2721, d3390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23678 (p : Pattern) (guard : d5855 p = 1) : d2722 p ≤ (0 : Int) + d3391 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2722, d3391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23677 p hg
    simpa only [d5855, d2722, d3391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2722, d3391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23608 p hg
    simpa only [d5855, d2722, d3391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23679 (p : Pattern) (guard : d5855 p = 1) : d2723 p ≤ (0 : Int) + d3392 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2723, d3392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23678 p hg
    simpa only [d2723, d3392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2723, d3392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23615 p hg
    simpa only [d2723, d3392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23680 (p : Pattern) (guard : d5855 p = 1) : d2724 p ≤ (0 : Int) + d3393 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2724, d3393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23679 p hg
    simpa only [d2724, d3393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2724, d3393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23622 p hg
    simpa only [d2724, d3393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23681 (p : Pattern) (guard : d5843 p = 1) : d3 p ≤ (0 : Int) + d3 p := by
  omega
theorem compare23682 (p : Pattern) (guard : d5847 p = 1) : d116 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d116, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23681 p hg
    simpa only [d5847, d116, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d116, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d116, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23683 (p : Pattern) (guard : d5854 p = 1) : d2702 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23682 p hg
    simpa only [d5854, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18800 p hg
    simpa only [d5854, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23684 (p : Pattern) (guard : d5855 p = 1) : d2702 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23651 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23683 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23685 (p : Pattern) (guard : d5855 p = 1) : d2725 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23684 p hg
    simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23656 p hg
    simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23686 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23687 (p : Pattern) (guard : d5843 p = 1) : d1918 p ≤ (0 : Int) + d3 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d5843, d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23686 p hg
    simpa only [d5843, d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23688 (p : Pattern) (guard : d5847 p = 1) : d1919 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1919, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23687 p hg
    simpa only [d5847, d1919, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1919, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d1919, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23689 (p : Pattern) (guard : d5854 p = 1) : d2726 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23688 p hg
    simpa only [d5854, d2726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18800 p hg
    simpa only [d5854, d2726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23690 (p : Pattern) (guard : d5855 p = 1) : d2727 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23651 p hg
    simpa only [d5855, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23689 p hg
    simpa only [d5855, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23691 (p : Pattern) (guard : d5855 p = 1) : d2728 p ≤ (0 : Int) + d3375 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2728, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23690 p hg
    simpa only [d2728, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2728, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2728, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23692 (p : Pattern) (guard : d5855 p = 1) : d2729 p ≤ (0 : Int) + d3394 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2729, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23685 p hg
    simpa only [d2729, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2729, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23691 p hg
    simpa only [d2729, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23693 (p : Pattern) (guard : d5855 p = 1) : d2730 p ≤ (0 : Int) + d3395 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2730, d3395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23680 p hg
    simpa only [d2730, d3395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2730, d3395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23692 p hg
    simpa only [d2730, d3395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23694 (p : Pattern) (guard : d5855 p = 1) : d2731 p ≤ (0 : Int) + d3396 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2731, d3396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23645 p hg
    simpa only [d2731, d3396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2731, d3396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23500 p hg
    simpa only [d2731, d3396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23695 (p : Pattern) (guard : d5855 p = 1) : d2732 p ≤ (0 : Int) + d3397 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2732, d3397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23693 p hg
    simpa only [d2732, d3397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2732, d3397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23694 p hg
    simpa only [d2732, d3397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23696 (p : Pattern) (guard : d5855 p = 1) : d2733 p ≤ (0 : Int) + d3398 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2733, d3398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23645 p hg
    simpa only [d2733, d3398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2733, d3398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23507 p hg
    simpa only [d2733, d3398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23697 (p : Pattern) (guard : d5855 p = 1) : d2734 p ≤ (0 : Int) + d3399 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2734, d3399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23696 p hg
    simpa only [d2734, d3399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2734, d3399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2734, d3399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23698 (p : Pattern) (guard : d5855 p = 1) : d2735 p ≤ (0 : Int) + d3400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2735, d3400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23695 p hg
    simpa only [d2735, d3400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2735, d3400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23697 p hg
    simpa only [d2735, d3400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23699 (p : Pattern) (guard : d5855 p = 1) : d2736 p ≤ (0 : Int) + d3401 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2736, d3401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23685 p hg
    simpa only [d2736, d3401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2736, d3401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2736, d3401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23700 (p : Pattern) (guard : d5855 p = 1) : d2737 p ≤ (0 : Int) + d3402 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2737, d3402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23666 p hg
    simpa only [d2737, d3402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2737, d3402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23699 p hg
    simpa only [d2737, d3402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23701 (p : Pattern) (guard : d5855 p = 1) : d2738 p ≤ (0 : Int) + d3403 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2738, d3403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23669 p hg
    simpa only [d2738, d3403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2738, d3403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23515 p hg
    simpa only [d2738, d3403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23702 (p : Pattern) (guard : d5855 p = 1) : d2739 p ≤ (0 : Int) + d3404 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2739, d3404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23700 p hg
    simpa only [d2739, d3404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2739, d3404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23701 p hg
    simpa only [d2739, d3404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23703 (p : Pattern) (guard : d5855 p = 1) : d2740 p ≤ (0 : Int) + d3405 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2740, d3405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23669 p hg
    simpa only [d2740, d3405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2740, d3405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23517 p hg
    simpa only [d2740, d3405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23704 (p : Pattern) (guard : d5855 p = 1) : d2741 p ≤ (0 : Int) + d3406 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2741, d3406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23703 p hg
    simpa only [d2741, d3406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2741, d3406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2741, d3406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23705 (p : Pattern) (guard : d5855 p = 1) : d2742 p ≤ (0 : Int) + d3407 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2742, d3407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23702 p hg
    simpa only [d2742, d3407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2742, d3407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23704 p hg
    simpa only [d2742, d3407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23706 (p : Pattern) (guard : d5855 p = 1) : d2743 p ≤ (0 : Int) + d3408 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2743, d3408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23698 p hg
    simpa only [d2743, d3408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2743, d3408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23705 p hg
    simpa only [d2743, d3408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23707 (p : Pattern) (guard : d5855 p = 1) : d2744 p ≤ (0 : Int) + d3409 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2744, d3409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23675 p hg
    simpa only [d2744, d3409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2744, d3409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23706 p hg
    simpa only [d2744, d3409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23708 (p : Pattern) (guard : d5855 p = 1) : d2745 p ≤ (0 : Int) + d3362 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2745, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23615 p hg
    simpa only [d2745, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2745, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2745, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23709 (p : Pattern) (guard : d5855 p = 1) : d2746 p ≤ (0 : Int) + d3364 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2746, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23625 p hg
    simpa only [d2746, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2746, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23708 p hg
    simpa only [d2746, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23710 (p : Pattern) (guard : d5855 p = 1) : d2747 p ≤ (0 : Int) + d3367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2747, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23637 p hg
    simpa only [d2747, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2747, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2747, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23711 (p : Pattern) (guard : d5855 p = 1) : d2748 p ≤ (0 : Int) + d3368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2748, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23638 p hg
    simpa only [d2748, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2748, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23710 p hg
    simpa only [d2748, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23712 (p : Pattern) (guard : d5855 p = 1) : d2749 p ≤ (0 : Int) + d3369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2749, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23709 p hg
    simpa only [d2749, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2749, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23711 p hg
    simpa only [d2749, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23713 (p : Pattern) (guard : d5855 p = 1) : d2750 p ≤ (0 : Int) + d3410 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2750, d3410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23709 p hg
    simpa only [d2750, d3410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2750, d3410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23712 p hg
    simpa only [d2750, d3410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23714 (p : Pattern) (guard : d5855 p = 1) : d2751 p ≤ (0 : Int) + d3372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2751, d3372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23712 p hg
    simpa only [d2751, d3372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2751, d3372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23648 p hg
    simpa only [d2751, d3372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23715 (p : Pattern) (guard : d5855 p = 1) : d2752 p ≤ (0 : Int) + d3411 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2752, d3411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23713 p hg
    simpa only [d2752, d3411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2752, d3411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23714 p hg
    simpa only [d2752, d3411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23716 (p : Pattern) (guard : d5855 p = 1) : d2753 p ≤ (0 : Int) + d3394 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2753, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23685 p hg
    simpa only [d2753, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2753, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23657 p hg
    simpa only [d2753, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23717 (p : Pattern) (guard : d5843 p = 1) : d7 p ≤ (0 : Int) + d7 p := by
  omega
theorem compare23718 (p : Pattern) (guard : d5847 p = 1) : d120 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d120, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23717 p hg
    simpa only [d5847, d120, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d120, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5847, d120, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23719 (p : Pattern) (guard : d5854 p = 1) : d2707 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23718 p hg
    simpa only [d5854, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18804 p hg
    simpa only [d5854, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23720 (p : Pattern) (guard : d5855 p = 1) : d2707 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23659 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23719 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23721 (p : Pattern) (guard : d5855 p = 1) : d2754 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23720 p hg
    simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23664 p hg
    simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23722 (p : Pattern) (guard : d5855 p = 1) : d2755 p ≤ (0 : Int) + d3412 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2755, d3412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23721 p hg
    simpa only [d2755, d3412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2755, d3412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23665 p hg
    simpa only [d2755, d3412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23723 (p : Pattern) (guard : d5855 p = 1) : d2756 p ≤ (0 : Int) + d3413 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2756, d3413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23716 p hg
    simpa only [d2756, d3413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2756, d3413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23722 p hg
    simpa only [d2756, d3413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23724 (p : Pattern) (guard : d5855 p = 1) : d2757 p ≤ (0 : Int) + d3414 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2757, d3414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23723 p hg
    simpa only [d2757, d3414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2757, d3414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2757, d3414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23725 (p : Pattern) (guard : d5855 p = 1) : d2758 p ≤ (0 : Int) + d3415 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2758, d3415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23724 p hg
    simpa only [d2758, d3415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2758, d3415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2758, d3415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23726 (p : Pattern) (guard : d5855 p = 1) : d2759 p ≤ (0 : Int) + d3416 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2759, d3416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23715 p hg
    simpa only [d2759, d3416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2759, d3416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23725 p hg
    simpa only [d2759, d3416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23727 (p : Pattern) (guard : d5855 p = 1) : d2760 p ≤ (0 : Int) + d3417 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2760, d3417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23709 p hg
    simpa only [d2760, d3417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2760, d3417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23716 p hg
    simpa only [d2760, d3417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23728 (p : Pattern) (guard : d5855 p = 1) : d2761 p ≤ (0 : Int) + d3396 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2761, d3396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23711 p hg
    simpa only [d2761, d3396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2761, d3396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23500 p hg
    simpa only [d2761, d3396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23729 (p : Pattern) (guard : d5855 p = 1) : d2762 p ≤ (0 : Int) + d3418 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2762, d3418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23727 p hg
    simpa only [d2762, d3418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2762, d3418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23728 p hg
    simpa only [d2762, d3418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23730 (p : Pattern) (guard : d5855 p = 1) : d2763 p ≤ (0 : Int) + d3398 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2763, d3398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23711 p hg
    simpa only [d2763, d3398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2763, d3398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23507 p hg
    simpa only [d2763, d3398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23731 (p : Pattern) (guard : d5855 p = 1) : d2764 p ≤ (0 : Int) + d3399 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2764, d3399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23730 p hg
    simpa only [d2764, d3399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2764, d3399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2764, d3399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23732 (p : Pattern) (guard : d5855 p = 1) : d2765 p ≤ (0 : Int) + d3419 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2765, d3419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23729 p hg
    simpa only [d2765, d3419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2765, d3419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23731 p hg
    simpa only [d2765, d3419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23733 (p : Pattern) (guard : d5855 p = 1) : d2766 p ≤ (0 : Int) + d3420 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2766, d3420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23722 p hg
    simpa only [d2766, d3420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2766, d3420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2766, d3420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23734 (p : Pattern) (guard : d5855 p = 1) : d2767 p ≤ (0 : Int) + d3421 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2767, d3421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23733 p hg
    simpa only [d2767, d3421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2767, d3421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2767, d3421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23735 (p : Pattern) (guard : d5855 p = 1) : d2768 p ≤ (0 : Int) + d3422 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2768, d3422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23734 p hg
    simpa only [d2768, d3422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2768, d3422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2768, d3422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23736 (p : Pattern) (guard : d5855 p = 1) : d2769 p ≤ (0 : Int) + d3423 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2769, d3423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23732 p hg
    simpa only [d2769, d3423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2769, d3423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23735 p hg
    simpa only [d2769, d3423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23737 (p : Pattern) (guard : d5855 p = 1) : d2770 p ≤ (0 : Int) + d3424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2770, d3424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23726 p hg
    simpa only [d2770, d3424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2770, d3424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23736 p hg
    simpa only [d2770, d3424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23738 (p : Pattern) (guard : d5855 p = 1) : d2771 p ≤ (0 : Int) + d3425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2771, d3425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23707 p hg
    simpa only [d2771, d3425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2771, d3425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23737 p hg
    simpa only [d2771, d3425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23739 (p : Pattern) (guard : d5855 p = 1) : d2772 p ≤ (0 : Int) + d3426 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2772, d3426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23648 p hg
    simpa only [d2772, d3426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2772, d3426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2772, d3426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23740 (p : Pattern) (guard : d5855 p = 1) : d2773 p ≤ (0 : Int) + d3427 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2773, d3427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23739 p hg
    simpa only [d2773, d3427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2773, d3427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2773, d3427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23741 (p : Pattern) (guard : d5855 p = 1) : d2774 p ≤ (0 : Int) + d3428 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2774, d3428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23740 p hg
    simpa only [d2774, d3428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2774, d3428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2774, d3428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23742 (p : Pattern) (guard : d5855 p = 1) : d2775 p ≤ (0 : Int) + d3429 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2775, d3429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23741 p hg
    simpa only [d2775, d3429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2775, d3429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2775, d3429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23743 (p : Pattern) (guard : d5855 p = 1) : d2776 p ≤ (0 : Int) + d3430 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2776, d3430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23737 p hg
    simpa only [d2776, d3430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2776, d3430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23742 p hg
    simpa only [d2776, d3430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23744 (p : Pattern) (guard : d5855 p = 1) : d2777 p ≤ (0 : Int) + d3431 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2777, d3431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23738 p hg
    simpa only [d2777, d3431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2777, d3431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23743 p hg
    simpa only [d2777, d3431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23745 (p : Pattern) (guard : d5855 p = 1) : d2778 p ≤ (0 : Int) + d3410 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2778, d3410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23626 p hg
    simpa only [d2778, d3410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2778, d3410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23646 p hg
    simpa only [d2778, d3410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23746 (p : Pattern) (guard : d5855 p = 1) : d2779 p ≤ (0 : Int) + d3411 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2779, d3411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23745 p hg
    simpa only [d2779, d3411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2779, d3411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23649 p hg
    simpa only [d2779, d3411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23747 (p : Pattern) (guard : d5855 p = 1) : d2780 p ≤ (0 : Int) + d3432 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2780, d3432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23746 p hg
    simpa only [d2780, d3432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2780, d3432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23674 p hg
    simpa only [d2780, d3432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23748 (p : Pattern) (guard : d5855 p = 1) : d2781 p ≤ (0 : Int) + d3417 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2781, d3417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23626 p hg
    simpa only [d2781, d3417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2781, d3417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23692 p hg
    simpa only [d2781, d3417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23749 (p : Pattern) (guard : d5855 p = 1) : d2782 p ≤ (0 : Int) + d3418 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2782, d3418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23748 p hg
    simpa only [d2782, d3418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2782, d3418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23694 p hg
    simpa only [d2782, d3418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23750 (p : Pattern) (guard : d5855 p = 1) : d2783 p ≤ (0 : Int) + d3419 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2783, d3419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23749 p hg
    simpa only [d2783, d3419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2783, d3419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23697 p hg
    simpa only [d2783, d3419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23751 (p : Pattern) (guard : d5855 p = 1) : d2784 p ≤ (0 : Int) + d3433 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2784, d3433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23750 p hg
    simpa only [d2784, d3433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2784, d3433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23705 p hg
    simpa only [d2784, d3433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23752 (p : Pattern) (guard : d5855 p = 1) : d2785 p ≤ (0 : Int) + d3434 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2785, d3434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23747 p hg
    simpa only [d2785, d3434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2785, d3434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23751 p hg
    simpa only [d2785, d3434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23753 (p : Pattern) (guard : d5855 p = 1) : d2786 p ≤ (0 : Int) + d3435 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2786, d3435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23752 p hg
    simpa only [d2786, d3435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2786, d3435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23737 p hg
    simpa only [d2786, d3435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23754 (p : Pattern) (guard : d5855 p = 1) : d2787 p ≤ (0 : Int) + d3436 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2787, d3436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23737 p hg
    simpa only [d2787, d3436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2787, d3436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2787, d3436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23755 (p : Pattern) (guard : d5855 p = 1) : d2788 p ≤ (0 : Int) + d3437 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2788, d3437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23753 p hg
    simpa only [d2788, d3437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2788, d3437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23754 p hg
    simpa only [d2788, d3437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23756 (p : Pattern) (guard : d5855 p = 1) : d2789 p ≤ (0 : Int) + d3438 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2789, d3438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23744 p hg
    simpa only [d2789, d3438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2789, d3438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23755 p hg
    simpa only [d2789, d3438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23757 (p : Pattern) (guard : d5855 p = 1) : d2790 p ≤ (0 : Int) + d3439 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2790, d3439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23579 p hg
    simpa only [d2790, d3439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2790, d3439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23756 p hg
    simpa only [d2790, d3439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23758 (p : Pattern) (guard : d5855 p = 1) : d2791 p ≤ (0 : Int) + d3440 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2791, d3440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23603 p hg
    simpa only [d2791, d3440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2791, d3440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23757 p hg
    simpa only [d2791, d3440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23759 (p : Pattern) (guard : d5855 p = 1) : d2792 p ≤ (0 : Int) + d3441 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2792, d3441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23477 p hg
    simpa only [d2792, d3441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2792, d3441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23447 p hg
    simpa only [d2792, d3441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23760 (p : Pattern) (guard : d5855 p = 1) : d2793 p ≤ (0 : Int) + d3442 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2793, d3442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23534 p hg
    simpa only [d2793, d3442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2793, d3442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23759 p hg
    simpa only [d2793, d3442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23761 (p : Pattern) (guard : d5855 p = 1) : d2794 p ≤ (0 : Int) + d3443 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2794, d3443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23477 p hg
    simpa only [d2794, d3443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2794, d3443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23456 p hg
    simpa only [d2794, d3443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23762 (p : Pattern) (guard : d5855 p = 1) : d2795 p ≤ (0 : Int) + d3444 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2795, d3444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23539 p hg
    simpa only [d2795, d3444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2795, d3444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2795, d3444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23763 (p : Pattern) (guard : d5855 p = 1) : d2796 p ≤ (0 : Int) + d3445 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2796, d3445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23761 p hg
    simpa only [d2796, d3445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2796, d3445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23762 p hg
    simpa only [d2796, d3445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23764 (p : Pattern) (guard : d5855 p = 1) : d2797 p ≤ (0 : Int) + d3446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2797, d3446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23760 p hg
    simpa only [d2797, d3446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2797, d3446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23763 p hg
    simpa only [d2797, d3446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23765 (p : Pattern) (guard : d5855 p = 1) : d2798 p ≤ (0 : Int) + d3447 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2798, d3447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23511 p hg
    simpa only [d2798, d3447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2798, d3447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23762 p hg
    simpa only [d2798, d3447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23766 (p : Pattern) (guard : d5855 p = 1) : d2799 p ≤ (0 : Int) + d3448 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2799, d3448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23765 p hg
    simpa only [d2799, d3448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2799, d3448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23518 p hg
    simpa only [d2799, d3448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23767 (p : Pattern) (guard : d5855 p = 1) : d2800 p ≤ (0 : Int) + d3449 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2800, d3449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23764 p hg
    simpa only [d2800, d3449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2800, d3449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23766 p hg
    simpa only [d2800, d3449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23768 (p : Pattern) (guard : d5855 p = 1) : d2801 p ≤ (0 : Int) + d3450 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2801, d3450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23533 p hg
    simpa only [d2801, d3450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2801, d3450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23767 p hg
    simpa only [d2801, d3450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23769 (p : Pattern) (guard : d5855 p = 1) : d2802 p ≤ (0 : Int) + d3451 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2802, d3451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23759 p hg
    simpa only [d2802, d3451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2802, d3451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23458 p hg
    simpa only [d2802, d3451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23770 (p : Pattern) (guard : d5855 p = 1) : d2803 p ≤ (0 : Int) + d3452 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2803, d3452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23762 p hg
    simpa only [d2803, d3452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2803, d3452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23517 p hg
    simpa only [d2803, d3452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23771 (p : Pattern) (guard : d5855 p = 1) : d2804 p ≤ (0 : Int) + d3453 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2804, d3453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23769 p hg
    simpa only [d2804, d3453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2804, d3453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23770 p hg
    simpa only [d2804, d3453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23772 (p : Pattern) (guard : d5855 p = 1) : d2805 p ≤ (0 : Int) + d3454 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2805, d3454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23762 p hg
    simpa only [d2805, d3454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2805, d3454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2805, d3454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23773 (p : Pattern) (guard : d5855 p = 1) : d2806 p ≤ (0 : Int) + d3455 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2806, d3455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23772 p hg
    simpa only [d2806, d3455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2806, d3455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2806, d3455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23774 (p : Pattern) (guard : d5855 p = 1) : d2807 p ≤ (0 : Int) + d3456 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2807, d3456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23771 p hg
    simpa only [d2807, d3456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2807, d3456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23773 p hg
    simpa only [d2807, d3456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23775 (p : Pattern) (guard : d5855 p = 1) : d2808 p ≤ (0 : Int) + d3457 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2808, d3457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23550 p hg
    simpa only [d2808, d3457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2808, d3457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23774 p hg
    simpa only [d2808, d3457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23776 (p : Pattern) (guard : d5855 p = 1) : d2809 p ≤ (0 : Int) + d3458 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2809, d3458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23768 p hg
    simpa only [d2809, d3458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2809, d3458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23775 p hg
    simpa only [d2809, d3458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23777 (p : Pattern) (guard : d5855 p = 1) : d2810 p ≤ (0 : Int) + d3459 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2810, d3459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23524 p hg
    simpa only [d2810, d3459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2810, d3459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23541 p hg
    simpa only [d2810, d3459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23778 (p : Pattern) (guard : d5855 p = 1) : d2811 p ≤ (0 : Int) + d3460 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2811, d3460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23777 p hg
    simpa only [d2811, d3460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2811, d3460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23542 p hg
    simpa only [d2811, d3460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23779 (p : Pattern) (guard : d5851 p = 1) : d2812 p ≤ (0 : Int) + d3461 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17897 p hg
    simpa only [d5851, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18891 p hg
    simpa only [d5851, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23780 (p : Pattern) (guard : d5843 p = 1) : d8 p ≤ (0 : Int) + d8 p := by
  omega
theorem compare23781 (p : Pattern) (guard : d5847 p = 1) : d191 p ≤ (0 : Int) + d3461 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d191, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23780 p hg
    simpa only [d5847, d191, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d191, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5847, d191, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23782 (p : Pattern) (guard : d5854 p = 1) : d2812 p ≤ (0 : Int) + d3461 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23781 p hg
    simpa only [d5854, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18891 p hg
    simpa only [d5854, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23783 (p : Pattern) (guard : d5855 p = 1) : d2812 p ≤ (0 : Int) + d3461 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23779 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23782 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23784 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23785 (p : Pattern) (guard : d5843 p = 1) : d190 p ≤ (0 : Int) + d8 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14750 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23784 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23786 (p : Pattern) (guard : d5847 p = 1) : d315 p ≤ (0 : Int) + d3461 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d315, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23785 p hg
    simpa only [d5847, d315, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d315, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d315, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23787 (p : Pattern) (guard : d5854 p = 1) : d320 p ≤ (0 : Int) + d3461 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23786 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18891 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23788 (p : Pattern) (guard : d5855 p = 1) : d2813 p ≤ (0 : Int) + d3461 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23779 p hg
    simpa only [d5855, d2813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23787 p hg
    simpa only [d5855, d2813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23789 (p : Pattern) (guard : d5855 p = 1) : d2814 p ≤ (0 : Int) + d3461 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23783 p hg
    simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23788 p hg
    simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23790 (p : Pattern) (guard : d5855 p = 1) : d2815 p ≤ (0 : Int) + d3462 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2815, d3462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23788 p hg
    simpa only [d2815, d3462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2815, d3462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2815, d3462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23791 (p : Pattern) (guard : d5855 p = 1) : d2816 p ≤ (0 : Int) + d3463 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2816, d3463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23789 p hg
    simpa only [d2816, d3463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2816, d3463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23790 p hg
    simpa only [d2816, d3463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23792 (p : Pattern) (guard : d5855 p = 1) : d2817 p ≤ (0 : Int) + d3464 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2817, d3464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23526 p hg
    simpa only [d2817, d3464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2817, d3464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23791 p hg
    simpa only [d2817, d3464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23793 (p : Pattern) (guard : d5855 p = 1) : d2818 p ≤ (0 : Int) + d3465 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2818, d3465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23792 p hg
    simpa only [d2818, d3465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2818, d3465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2818, d3465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23794 (p : Pattern) (guard : d5855 p = 1) : d2819 p ≤ (0 : Int) + d3466 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2819, d3466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23793 p hg
    simpa only [d2819, d3466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2819, d3466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2819, d3466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23795 (p : Pattern) (guard : d5855 p = 1) : d2820 p ≤ (0 : Int) + d3467 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2820, d3467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23778 p hg
    simpa only [d2820, d3467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2820, d3467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23794 p hg
    simpa only [d2820, d3467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23796 (p : Pattern) (guard : d5855 p = 1) : d2821 p ≤ (0 : Int) + d3468 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2821, d3468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23526 p hg
    simpa only [d2821, d3468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2821, d3468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23507 p hg
    simpa only [d2821, d3468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23797 (p : Pattern) (guard : d5855 p = 1) : d2822 p ≤ (0 : Int) + d3469 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2822, d3469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23534 p hg
    simpa only [d2822, d3469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2822, d3469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23796 p hg
    simpa only [d2822, d3469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23798 (p : Pattern) (guard : d5855 p = 1) : d2823 p ≤ (0 : Int) + d3470 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2823, d3470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23797 p hg
    simpa only [d2823, d3470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2823, d3470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23552 p hg
    simpa only [d2823, d3470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23799 (p : Pattern) (guard : d5855 p = 1) : d2824 p ≤ (0 : Int) + d3471 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2824, d3471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23791 p hg
    simpa only [d2824, d3471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2824, d3471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2824, d3471, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
