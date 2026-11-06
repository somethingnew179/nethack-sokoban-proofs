/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons026
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3780 (p : Pattern) (guard : d1248 p = 1) : d360 p ≤ (0 : Int) + d720 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d360, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3746 p hg
    simpa only [d360, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d360, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3779 p hg
    simpa only [d360, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3781 (p : Pattern) (guard : d1248 p = 1) : d361 p ≤ (0 : Int) + d706 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3469 p hg
    simpa only [d1248, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3473 p hg
    simpa only [d1248, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3782 (p : Pattern) (guard : d1248 p = 1) : d362 p ≤ (0 : Int) + d706 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3781 p hg
    simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3761 p hg
    simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3783 (p : Pattern) (guard : d1248 p = 1) : d363 p ≤ (0 : Int) + d706 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3781 p hg
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3782 p hg
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3784 (p : Pattern) (guard : d1248 p = 1) : d364 p ≤ (0 : Int) + d721 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d364, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3780 p hg
    simpa only [d364, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d364, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3783 p hg
    simpa only [d364, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3785 (p : Pattern) (guard : d1248 p = 1) : d365 p ≤ (0 : Int) + d722 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d365, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3775 p hg
    simpa only [d365, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d365, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3764 p hg
    simpa only [d365, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3786 (p : Pattern) (guard : d1248 p = 1) : d366 p ≤ (0 : Int) + d723 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d366, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3775 p hg
    simpa only [d366, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d366, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3785 p hg
    simpa only [d366, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3787 (p : Pattern) (guard : d1248 p = 1) : d367 p ≤ (0 : Int) + d724 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d367, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3766 p hg
    simpa only [d367, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d367, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3786 p hg
    simpa only [d367, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3788 (p : Pattern) (guard : d1248 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare3789 (p : Pattern) (guard : d1248 p = 1) : d368 p ≤ (0 : Int) + d725 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d368, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3781 p hg
    simpa only [d368, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d368, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3788 p hg
    simpa only [d368, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3790 (p : Pattern) (guard : d1248 p = 1) : d369 p ≤ (0 : Int) + d726 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d369, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3781 p hg
    simpa only [d369, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d369, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3789 p hg
    simpa only [d369, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3791 (p : Pattern) (guard : d1248 p = 1) : d370 p ≤ (0 : Int) + d705 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3468 p hg
    simpa only [d1248, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3451 p hg
    simpa only [d1248, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3792 (p : Pattern) (guard : d1248 p = 1) : d371 p ≤ (0 : Int) + d727 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d371, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3791 p hg
    simpa only [d371, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d371, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3788 p hg
    simpa only [d371, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3793 (p : Pattern) (guard : d1248 p = 1) : d372 p ≤ (0 : Int) + d728 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d372, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3791 p hg
    simpa only [d372, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d372, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3792 p hg
    simpa only [d372, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3794 (p : Pattern) (guard : d1248 p = 1) : d373 p ≤ (0 : Int) + d729 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d373, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3790 p hg
    simpa only [d373, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d373, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3793 p hg
    simpa only [d373, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3795 (p : Pattern) (guard : d1248 p = 1) : d374 p ≤ (0 : Int) + d730 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d374, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3787 p hg
    simpa only [d374, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d374, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3794 p hg
    simpa only [d374, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3796 (p : Pattern) (guard : d1248 p = 1) : d375 p ≤ (0 : Int) + d731 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d375, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3784 p hg
    simpa only [d375, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d375, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3795 p hg
    simpa only [d375, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3797 (p : Pattern) (guard : d1248 p = 1) : d376 p ≤ (0 : Int) + d732 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d376, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3774 p hg
    simpa only [d376, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d376, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3796 p hg
    simpa only [d376, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3798 (p : Pattern) (guard : d1248 p = 1) : d377 p ≤ (0 : Int) + d733 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d377, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3766 p hg
    simpa only [d377, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d377, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3772 p hg
    simpa only [d377, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3799 (p : Pattern) (guard : d1248 p = 1) : d378 p ≤ (0 : Int) + d734 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d378, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3758 p hg
    simpa only [d378, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d378, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3798 p hg
    simpa only [d378, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3800 (p : Pattern) (guard : d1248 p = 1) : d379 p ≤ (0 : Int) + d705 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3791 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3764 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3801 (p : Pattern) (guard : d1248 p = 1) : d380 p ≤ (0 : Int) + d705 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3791 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3800 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3802 (p : Pattern) (guard : d1248 p = 1) : d381 p ≤ (0 : Int) + d735 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d381, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3783 p hg
    simpa only [d381, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d381, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3801 p hg
    simpa only [d381, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3803 (p : Pattern) (guard : d1248 p = 1) : d382 p ≤ (0 : Int) + d736 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d382, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3780 p hg
    simpa only [d382, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d382, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3802 p hg
    simpa only [d382, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3804 (p : Pattern) (guard : d1248 p = 1) : d383 p ≤ (0 : Int) + d737 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d383, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3766 p hg
    simpa only [d383, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d383, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3771 p hg
    simpa only [d383, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3805 (p : Pattern) (guard : d1248 p = 1) : d384 p ≤ (0 : Int) + d738 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d384, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3793 p hg
    simpa only [d384, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d384, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3788 p hg
    simpa only [d384, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3806 (p : Pattern) (guard : d1248 p = 1) : d385 p ≤ (0 : Int) + d739 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d385, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3804 p hg
    simpa only [d385, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d385, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3805 p hg
    simpa only [d385, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3807 (p : Pattern) (guard : d1248 p = 1) : d386 p ≤ (0 : Int) + d740 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d386, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3803 p hg
    simpa only [d386, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d386, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3806 p hg
    simpa only [d386, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3808 (p : Pattern) (guard : d1248 p = 1) : d387 p ≤ (0 : Int) + d741 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d387, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3799 p hg
    simpa only [d387, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d387, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3807 p hg
    simpa only [d387, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3809 (p : Pattern) (guard : d1248 p = 1) : d388 p ≤ (0 : Int) + d742 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d388, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3797 p hg
    simpa only [d388, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d388, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3808 p hg
    simpa only [d388, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3810 (p : Pattern) (guard : d0 p = 1) : d328 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3811 (p : Pattern) (guard : d984 p = 1) : d328 p ≤ (0 : Int) + d293 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3644 p hg
    simpa only [d984, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3810 p hg
    simpa only [d984, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3812 (p : Pattern) (guard : d0 p = 1) : d329 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3813 (p : Pattern) (guard : d984 p = 1) : d330 p ≤ (0 : Int) + d293 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d330, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3644 p hg
    simpa only [d984, d330, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d330, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3812 p hg
    simpa only [d984, d330, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3814 (p : Pattern) (guard : d984 p = 1) : d331 p ≤ (0 : Int) + d293 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3811 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3813 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3815 (p : Pattern) (guard : d0 p = 1) : d332 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3816 (p : Pattern) (guard : d984 p = 1) : d332 p ≤ (0 : Int) + d294 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3653 p hg
    simpa only [d984, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3815 p hg
    simpa only [d984, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3817 (p : Pattern) (guard : d0 p = 1) : d333 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3818 (p : Pattern) (guard : d984 p = 1) : d334 p ≤ (0 : Int) + d294 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d334, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3653 p hg
    simpa only [d984, d334, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d334, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3817 p hg
    simpa only [d984, d334, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3819 (p : Pattern) (guard : d984 p = 1) : d335 p ≤ (0 : Int) + d294 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3816 p hg
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3818 p hg
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3820 (p : Pattern) (guard : d0 p = 1) : d336 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3821 (p : Pattern) (guard : d984 p = 1) : d336 p ≤ (0 : Int) + d295 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3662 p hg
    simpa only [d984, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3820 p hg
    simpa only [d984, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3822 (p : Pattern) (guard : d0 p = 1) : d337 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3823 (p : Pattern) (guard : d984 p = 1) : d338 p ≤ (0 : Int) + d295 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d338, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3662 p hg
    simpa only [d984, d338, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d338, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3822 p hg
    simpa only [d984, d338, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3824 (p : Pattern) (guard : d984 p = 1) : d339 p ≤ (0 : Int) + d295 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3821 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3823 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3825 (p : Pattern) (guard : d984 p = 1) : d340 p ≤ (0 : Int) + d296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d340, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3819 p hg
    simpa only [d340, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d340, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3824 p hg
    simpa only [d340, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3826 (p : Pattern) (guard : d984 p = 1) : d341 p ≤ (0 : Int) + d297 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d341, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3814 p hg
    simpa only [d341, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d341, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3825 p hg
    simpa only [d341, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3827 (p : Pattern) (guard : d0 p = 1) : d342 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3828 (p : Pattern) (guard : d984 p = 1) : d343 p ≤ (0 : Int) + d293 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d343, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3644 p hg
    simpa only [d984, d343, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d343, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3827 p hg
    simpa only [d984, d343, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3829 (p : Pattern) (guard : d984 p = 1) : d344 p ≤ (0 : Int) + d293 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3811 p hg
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3828 p hg
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3830 (p : Pattern) (guard : d0 p = 1) : d345 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3831 (p : Pattern) (guard : d984 p = 1) : d346 p ≤ (0 : Int) + d298 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d346, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3644 p hg
    simpa only [d984, d346, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d346, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3830 p hg
    simpa only [d984, d346, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3832 (p : Pattern) (guard : d984 p = 1) : d347 p ≤ (0 : Int) + d299 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d347, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3811 p hg
    simpa only [d347, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d347, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3831 p hg
    simpa only [d347, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3833 (p : Pattern) (guard : d984 p = 1) : d348 p ≤ (0 : Int) + d300 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d348, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3829 p hg
    simpa only [d348, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d348, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3832 p hg
    simpa only [d348, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3834 (p : Pattern) (guard : d0 p = 1) : d345 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3835 (p : Pattern) (guard : d984 p = 1) : d349 p ≤ (0 : Int) + d294 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d349, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3653 p hg
    simpa only [d984, d349, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d349, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3834 p hg
    simpa only [d984, d349, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3836 (p : Pattern) (guard : d984 p = 1) : d350 p ≤ (0 : Int) + d294 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3816 p hg
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3835 p hg
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3837 (p : Pattern) (guard : d984 p = 1) : d351 p ≤ (0 : Int) + d295 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d351, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3662 p hg
    simpa only [d984, d351, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d351, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3834 p hg
    simpa only [d984, d351, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3838 (p : Pattern) (guard : d984 p = 1) : d352 p ≤ (0 : Int) + d295 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3821 p hg
    simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3837 p hg
    simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3839 (p : Pattern) (guard : d984 p = 1) : d353 p ≤ (0 : Int) + d296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d353, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3836 p hg
    simpa only [d353, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d353, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3838 p hg
    simpa only [d353, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3840 (p : Pattern) (guard : d984 p = 1) : d354 p ≤ (0 : Int) + d301 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d354, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3833 p hg
    simpa only [d354, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d354, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3839 p hg
    simpa only [d354, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3841 (p : Pattern) (guard : d984 p = 1) : d355 p ≤ (0 : Int) + d302 p := by
  cases selected : p 106 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d355, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3826 p hg
    simpa only [d355, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d355, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3840 p hg
    simpa only [d355, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3842 (p : Pattern) (guard : d0 p = 1) : d356 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3843 (p : Pattern) (guard : d984 p = 1) : d356 p ≤ (0 : Int) + d303 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3689 p hg
    simpa only [d984, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3842 p hg
    simpa only [d984, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3844 (p : Pattern) (guard : d0 p = 1) : d357 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3845 (p : Pattern) (guard : d984 p = 1) : d358 p ≤ (0 : Int) + d304 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d358, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3689 p hg
    simpa only [d984, d358, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d358, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3844 p hg
    simpa only [d984, d358, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3846 (p : Pattern) (guard : d984 p = 1) : d359 p ≤ (0 : Int) + d305 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d359, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3843 p hg
    simpa only [d359, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d359, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3845 p hg
    simpa only [d359, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3847 (p : Pattern) (guard : d984 p = 1) : d360 p ≤ (0 : Int) + d306 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d360, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3814 p hg
    simpa only [d360, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d360, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3846 p hg
    simpa only [d360, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3848 (p : Pattern) (guard : d0 p = 1) : d361 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3849 (p : Pattern) (guard : d984 p = 1) : d361 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3699 p hg
    simpa only [d984, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3848 p hg
    simpa only [d984, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3850 (p : Pattern) (guard : d0 p = 1) : d342 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3851 (p : Pattern) (guard : d984 p = 1) : d362 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d362, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3699 p hg
    simpa only [d984, d362, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d362, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3850 p hg
    simpa only [d984, d362, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3852 (p : Pattern) (guard : d984 p = 1) : d363 p ≤ (0 : Int) + d307 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3849 p hg
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3851 p hg
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3853 (p : Pattern) (guard : d984 p = 1) : d364 p ≤ (0 : Int) + d308 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d364, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3847 p hg
    simpa only [d364, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d364, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3852 p hg
    simpa only [d364, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3854 (p : Pattern) (guard : d0 p = 1) : d356 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3855 (p : Pattern) (guard : d984 p = 1) : d356 p ≤ (0 : Int) + d304 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3689 p hg
    simpa only [d984, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3854 p hg
    simpa only [d984, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3856 (p : Pattern) (guard : d984 p = 1) : d365 p ≤ (0 : Int) + d309 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d365, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3689 p hg
    simpa only [d984, d365, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d365, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3834 p hg
    simpa only [d984, d365, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3857 (p : Pattern) (guard : d984 p = 1) : d366 p ≤ (0 : Int) + d310 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d366, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3855 p hg
    simpa only [d366, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d366, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3856 p hg
    simpa only [d366, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3858 (p : Pattern) (guard : d984 p = 1) : d367 p ≤ (0 : Int) + d311 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d367, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3832 p hg
    simpa only [d367, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d367, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3857 p hg
    simpa only [d367, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3859 (p : Pattern) (guard : d984 p = 1) : d368 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d368, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3699 p hg
    simpa only [d984, d368, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d368, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d984, d368, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3860 (p : Pattern) (guard : d984 p = 1) : d369 p ≤ (0 : Int) + d307 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3849 p hg
    simpa only [d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3859 p hg
    simpa only [d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3861 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3862 (p : Pattern) (guard : d984 p = 1) : d370 p ≤ (0 : Int) + d312 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3710 p hg
    simpa only [d984, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3861 p hg
    simpa only [d984, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3863 (p : Pattern) (guard : d984 p = 1) : d371 p ≤ (0 : Int) + d312 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d371, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3710 p hg
    simpa only [d984, d371, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d371, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d984, d371, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3864 (p : Pattern) (guard : d984 p = 1) : d372 p ≤ (0 : Int) + d312 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3862 p hg
    simpa only [d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3863 p hg
    simpa only [d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3865 (p : Pattern) (guard : d984 p = 1) : d373 p ≤ (0 : Int) + d313 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d373, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3860 p hg
    simpa only [d373, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d373, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3864 p hg
    simpa only [d373, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3866 (p : Pattern) (guard : d984 p = 1) : d374 p ≤ (0 : Int) + d314 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d374, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3858 p hg
    simpa only [d374, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d374, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3865 p hg
    simpa only [d374, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3867 (p : Pattern) (guard : d984 p = 1) : d375 p ≤ (0 : Int) + d315 p := by
  cases selected : p 106 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d375, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3853 p hg
    simpa only [d375, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d375, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3866 p hg
    simpa only [d375, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3868 (p : Pattern) (guard : d984 p = 1) : d376 p ≤ (0 : Int) + d316 p := by
  cases selected : p 86 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d376, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3841 p hg
    simpa only [d376, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d376, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3867 p hg
    simpa only [d376, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3869 (p : Pattern) (guard : d0 p = 1) : d329 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3870 (p : Pattern) (guard : d984 p = 1) : d330 p ≤ (0 : Int) + d298 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d330, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3644 p hg
    simpa only [d984, d330, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d330, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3869 p hg
    simpa only [d984, d330, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3871 (p : Pattern) (guard : d984 p = 1) : d331 p ≤ (0 : Int) + d299 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d331, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3811 p hg
    simpa only [d331, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d331, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3870 p hg
    simpa only [d331, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3872 (p : Pattern) (guard : d984 p = 1) : d331 p ≤ (0 : Int) + d300 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3814 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3871 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3873 (p : Pattern) (guard : d984 p = 1) : d341 p ≤ (0 : Int) + d301 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d341, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3872 p hg
    simpa only [d341, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d341, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3825 p hg
    simpa only [d341, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3874 (p : Pattern) (guard : d0 p = 1) : d328 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3875 (p : Pattern) (guard : d984 p = 1) : d328 p ≤ (0 : Int) + d298 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3644 p hg
    simpa only [d984, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3874 p hg
    simpa only [d984, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3876 (p : Pattern) (guard : d984 p = 1) : d346 p ≤ (0 : Int) + d317 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d346, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3644 p hg
    simpa only [d984, d346, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d346, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3834 p hg
    simpa only [d984, d346, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3877 (p : Pattern) (guard : d984 p = 1) : d347 p ≤ (0 : Int) + d318 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d347, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3875 p hg
    simpa only [d347, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d347, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3876 p hg
    simpa only [d347, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3878 (p : Pattern) (guard : d984 p = 1) : d347 p ≤ (0 : Int) + d319 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3832 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3877 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3879 (p : Pattern) (guard : d984 p = 1) : d377 p ≤ (0 : Int) + d320 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d377, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3878 p hg
    simpa only [d377, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d377, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3839 p hg
    simpa only [d377, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3880 (p : Pattern) (guard : d984 p = 1) : d378 p ≤ (0 : Int) + d321 p := by
  cases selected : p 106 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d378, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3873 p hg
    simpa only [d378, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d378, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3879 p hg
    simpa only [d378, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3881 (p : Pattern) (guard : d0 p = 1) : d357 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3882 (p : Pattern) (guard : d984 p = 1) : d358 p ≤ (0 : Int) + d309 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d358, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3689 p hg
    simpa only [d984, d358, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d358, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3881 p hg
    simpa only [d984, d358, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3883 (p : Pattern) (guard : d984 p = 1) : d359 p ≤ (0 : Int) + d310 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d359, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3855 p hg
    simpa only [d359, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d359, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3882 p hg
    simpa only [d359, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3884 (p : Pattern) (guard : d984 p = 1) : d360 p ≤ (0 : Int) + d311 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d360, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3871 p hg
    simpa only [d360, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d360, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3883 p hg
    simpa only [d360, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3885 (p : Pattern) (guard : d984 p = 1) : d379 p ≤ (0 : Int) + d312 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d379, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3710 p hg
    simpa only [d984, d379, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d379, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3834 p hg
    simpa only [d984, d379, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3886 (p : Pattern) (guard : d984 p = 1) : d380 p ≤ (0 : Int) + d312 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3862 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3885 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3887 (p : Pattern) (guard : d984 p = 1) : d381 p ≤ (0 : Int) + d313 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d381, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3852 p hg
    simpa only [d381, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d381, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3886 p hg
    simpa only [d381, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3888 (p : Pattern) (guard : d984 p = 1) : d382 p ≤ (0 : Int) + d314 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d382, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3884 p hg
    simpa only [d382, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d382, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3887 p hg
    simpa only [d382, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3889 (p : Pattern) (guard : d984 p = 1) : d383 p ≤ (0 : Int) + d322 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d383, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3877 p hg
    simpa only [d383, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d383, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3838 p hg
    simpa only [d383, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3890 (p : Pattern) (guard : d984 p = 1) : d384 p ≤ (0 : Int) + d323 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d384, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3864 p hg
    simpa only [d384, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d384, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d384, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3891 (p : Pattern) (guard : d984 p = 1) : d385 p ≤ (0 : Int) + d324 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d385, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3889 p hg
    simpa only [d385, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d385, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3890 p hg
    simpa only [d385, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3892 (p : Pattern) (guard : d984 p = 1) : d386 p ≤ (0 : Int) + d325 p := by
  cases selected : p 106 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d386, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3888 p hg
    simpa only [d386, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d386, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3891 p hg
    simpa only [d386, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3893 (p : Pattern) (guard : d984 p = 1) : d387 p ≤ (0 : Int) + d326 p := by
  cases selected : p 86 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d387, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3880 p hg
    simpa only [d387, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d387, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3892 p hg
    simpa only [d387, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3894 (p : Pattern) (guard : d984 p = 1) : d388 p ≤ (0 : Int) + d327 p := by
  cases selected : p 80 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d388, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3868 p hg
    simpa only [d388, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d388, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3893 p hg
    simpa only [d388, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3895 (p : Pattern) (guard : d0 p = 1) : d328 p ≤ (2 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3896 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (2 : Int) + d16 p := by
  omega
theorem compare3897 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3898 (p : Pattern) (guard : d915 p = 1) : d328 p ≤ (2 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3896 p hg
    simpa only [d915, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3897 p hg
    simpa only [d915, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3899 (p : Pattern) (guard : d1150 p = 1) : d328 p ≤ (2 : Int) + d16 p := by
  cases selected : p 133 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3895 p hg
    simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3898 p hg
    simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3900 (p : Pattern) (guard : d0 p = 1) : d330 p ≤ (2 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3901 (p : Pattern) (guard : d1151 p = 1) : d331 p ≤ (2 : Int) + d16 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3899 p hg
    simpa only [d1151, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3900 p hg
    simpa only [d1151, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3902 (p : Pattern) (guard : d0 p = 1) : d332 p ≤ (2 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3903 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (2 : Int) + d15 p := by
  omega
theorem compare3904 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3905 (p : Pattern) (guard : d915 p = 1) : d332 p ≤ (2 : Int) + d15 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3903 p hg
    simpa only [d915, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3904 p hg
    simpa only [d915, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3906 (p : Pattern) (guard : d1150 p = 1) : d332 p ≤ (2 : Int) + d15 p := by
  cases selected : p 133 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3902 p hg
    simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3905 p hg
    simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3907 (p : Pattern) (guard : d0 p = 1) : d334 p ≤ (2 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3908 (p : Pattern) (guard : d1151 p = 1) : d335 p ≤ (2 : Int) + d15 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3906 p hg
    simpa only [d1151, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3907 p hg
    simpa only [d1151, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3909 (p : Pattern) (guard : d0 p = 1) : d336 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3910 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (2 : Int) + d53 p := by
  omega
theorem compare3911 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3912 (p : Pattern) (guard : d915 p = 1) : d336 p ≤ (2 : Int) + d53 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3910 p hg
    simpa only [d915, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3911 p hg
    simpa only [d915, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3913 (p : Pattern) (guard : d1150 p = 1) : d336 p ≤ (2 : Int) + d53 p := by
  cases selected : p 133 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3909 p hg
    simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3912 p hg
    simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3914 (p : Pattern) (guard : d0 p = 1) : d338 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3915 (p : Pattern) (guard : d1151 p = 1) : d339 p ≤ (2 : Int) + d53 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3913 p hg
    simpa only [d1151, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3914 p hg
    simpa only [d1151, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3916 (p : Pattern) (guard : d1151 p = 1) : d340 p ≤ (2 : Int) + d1152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d340, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3908 p hg
    simpa only [d340, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d340, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3915 p hg
    simpa only [d340, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3917 (p : Pattern) (guard : d1151 p = 1) : d341 p ≤ (2 : Int) + d1153 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d341, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3901 p hg
    simpa only [d341, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d341, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3916 p hg
    simpa only [d341, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3918 (p : Pattern) (guard : d0 p = 1) : d343 p ≤ (2 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3919 (p : Pattern) (guard : d1151 p = 1) : d344 p ≤ (2 : Int) + d16 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3899 p hg
    simpa only [d1151, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3918 p hg
    simpa only [d1151, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
