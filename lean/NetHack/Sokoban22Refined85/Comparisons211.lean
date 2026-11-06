/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons210
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare29540 (p : Pattern) (guard : d5850 p = 1) : d3789 p ≤ (0 : Int) + d2716 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3789, d2716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29531 p hg
    simpa only [d3789, d2716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3789, d2716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29539 p hg
    simpa only [d3789, d2716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29541 (p : Pattern) (guard : d5850 p = 1) : d3790 p ≤ (0 : Int) + d2717 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3790, d2717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29361 p hg
    simpa only [d3790, d2717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3790, d2717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3790, d2717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29542 (p : Pattern) (guard : d5850 p = 1) : d3791 p ≤ (0 : Int) + d2718 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3791, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29539 p hg
    simpa only [d3791, d2718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3791, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29541 p hg
    simpa only [d3791, d2718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29543 (p : Pattern) (guard : d5850 p = 1) : d3792 p ≤ (0 : Int) + d2719 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3792, d2719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29540 p hg
    simpa only [d3792, d2719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3792, d2719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29542 p hg
    simpa only [d3792, d2719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29544 (p : Pattern) (guard : d5850 p = 1) : d3793 p ≤ (0 : Int) + d2720 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3793, d2720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29508 p hg
    simpa only [d3793, d2720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3793, d2720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29543 p hg
    simpa only [d3793, d2720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29545 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d327 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29546 (p : Pattern) (guard : d5850 p = 1) : d102 p ≤ (0 : Int) + d2721 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d5850, d2721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29545 p hg
    simpa only [d5850, d2721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29547 (p : Pattern) (guard : d5850 p = 1) : d102 p ≤ (0 : Int) + d2722 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29546 p hg
    simpa only [d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29467 p hg
    simpa only [d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29548 (p : Pattern) (guard : d5850 p = 1) : d3745 p ≤ (0 : Int) + d2723 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3745, d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29547 p hg
    simpa only [d3745, d2723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3745, d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29474 p hg
    simpa only [d3745, d2723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29549 (p : Pattern) (guard : d5850 p = 1) : d3746 p ≤ (0 : Int) + d2724 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3746, d2724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29548 p hg
    simpa only [d3746, d2724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3746, d2724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29482 p hg
    simpa only [d3746, d2724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29550 (p : Pattern) (guard : d5850 p = 1) : d115 p ≤ (0 : Int) + d2702 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29514 p hg
    simpa only [d5850, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5850, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29551 (p : Pattern) (guard : d0 p = 1) : d3769 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29552 (p : Pattern) (guard : d5850 p = 1) : d3794 p ≤ (0 : Int) + d2702 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3794, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29514 p hg
    simpa only [d5850, d3794, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3794, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29551 p hg
    simpa only [d5850, d3794, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29553 (p : Pattern) (guard : d5850 p = 1) : d3769 p ≤ (0 : Int) + d2703 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29518 p hg
    simpa only [d5850, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29551 p hg
    simpa only [d5850, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29554 (p : Pattern) (guard : d5850 p = 1) : d3795 p ≤ (0 : Int) + d2704 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3795, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29552 p hg
    simpa only [d3795, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3795, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29553 p hg
    simpa only [d3795, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29555 (p : Pattern) (guard : d5850 p = 1) : d3796 p ≤ (0 : Int) + d2725 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3796, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29550 p hg
    simpa only [d3796, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3796, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29554 p hg
    simpa only [d3796, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29556 (p : Pattern) (guard : d0 p = 1) : d3797 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29557 (p : Pattern) (guard : d5850 p = 1) : d3798 p ≤ (0 : Int) + d2702 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3798, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29514 p hg
    simpa only [d5850, d3798, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3798, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29556 p hg
    simpa only [d5850, d3798, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29558 (p : Pattern) (guard : d5843 p = 1) : d115 p ≤ (0 : Int) + d1918 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d115, d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d5843, d115, d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d115, d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26436 p hg
    simpa only [d5843, d115, d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29559 (p : Pattern) (guard : d5843 p = 1) : d3797 p ≤ (0 : Int) + d1919 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3797, d1919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29558 p hg
    simpa only [d3797, d1919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3797, d1919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20166 p hg
    simpa only [d3797, d1919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29560 (p : Pattern) (guard : d5850 p = 1) : d3797 p ≤ (0 : Int) + d2726 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29559 p hg
    simpa only [d5850, d2726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29556 p hg
    simpa only [d5850, d2726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29561 (p : Pattern) (guard : d5850 p = 1) : d3799 p ≤ (0 : Int) + d2727 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3799, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29557 p hg
    simpa only [d3799, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3799, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29560 p hg
    simpa only [d3799, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29562 (p : Pattern) (guard : d5850 p = 1) : d3800 p ≤ (0 : Int) + d2728 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3800, d2728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29561 p hg
    simpa only [d3800, d2728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3800, d2728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3800, d2728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29563 (p : Pattern) (guard : d5850 p = 1) : d3801 p ≤ (0 : Int) + d2729 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3801, d2729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29555 p hg
    simpa only [d3801, d2729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3801, d2729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29562 p hg
    simpa only [d3801, d2729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29564 (p : Pattern) (guard : d5850 p = 1) : d3802 p ≤ (0 : Int) + d2730 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3802, d2730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29549 p hg
    simpa only [d3802, d2730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3802, d2730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29563 p hg
    simpa only [d3802, d2730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29565 (p : Pattern) (guard : d5850 p = 1) : d3803 p ≤ (0 : Int) + d2731 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3803, d2731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29503 p hg
    simpa only [d3803, d2731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3803, d2731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29348 p hg
    simpa only [d3803, d2731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29566 (p : Pattern) (guard : d5850 p = 1) : d3804 p ≤ (0 : Int) + d2732 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3804, d2732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29564 p hg
    simpa only [d3804, d2732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3804, d2732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29565 p hg
    simpa only [d3804, d2732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29567 (p : Pattern) (guard : d5850 p = 1) : d3805 p ≤ (0 : Int) + d2733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3805, d2733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29503 p hg
    simpa only [d3805, d2733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3805, d2733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29352 p hg
    simpa only [d3805, d2733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29568 (p : Pattern) (guard : d5850 p = 1) : d3806 p ≤ (0 : Int) + d2734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3806, d2734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29567 p hg
    simpa only [d3806, d2734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3806, d2734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3806, d2734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29569 (p : Pattern) (guard : d5850 p = 1) : d3807 p ≤ (0 : Int) + d2735 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3807, d2735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29566 p hg
    simpa only [d3807, d2735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3807, d2735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29568 p hg
    simpa only [d3807, d2735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29570 (p : Pattern) (guard : d5850 p = 1) : d3808 p ≤ (0 : Int) + d2725 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3808, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29550 p hg
    simpa only [d3808, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3808, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29520 p hg
    simpa only [d3808, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29571 (p : Pattern) (guard : d5850 p = 1) : d3809 p ≤ (0 : Int) + d2736 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3809, d2736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29570 p hg
    simpa only [d3809, d2736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3809, d2736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3809, d2736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29572 (p : Pattern) (guard : d5850 p = 1) : d3810 p ≤ (0 : Int) + d2737 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3810, d2737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29530 p hg
    simpa only [d3810, d2737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3810, d2737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29571 p hg
    simpa only [d3810, d2737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29573 (p : Pattern) (guard : d5850 p = 1) : d3811 p ≤ (0 : Int) + d2738 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3811, d2738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29538 p hg
    simpa only [d3811, d2738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3811, d2738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29361 p hg
    simpa only [d3811, d2738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29574 (p : Pattern) (guard : d5850 p = 1) : d3812 p ≤ (0 : Int) + d2739 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3812, d2739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29572 p hg
    simpa only [d3812, d2739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3812, d2739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29573 p hg
    simpa only [d3812, d2739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29575 (p : Pattern) (guard : d5850 p = 1) : d3813 p ≤ (0 : Int) + d2740 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3813, d2740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29538 p hg
    simpa only [d3813, d2740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3813, d2740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29363 p hg
    simpa only [d3813, d2740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29576 (p : Pattern) (guard : d5850 p = 1) : d3814 p ≤ (0 : Int) + d2741 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3814, d2741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29575 p hg
    simpa only [d3814, d2741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3814, d2741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3814, d2741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29577 (p : Pattern) (guard : d5850 p = 1) : d3815 p ≤ (0 : Int) + d2742 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3815, d2742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29574 p hg
    simpa only [d3815, d2742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3815, d2742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29576 p hg
    simpa only [d3815, d2742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29578 (p : Pattern) (guard : d5850 p = 1) : d3816 p ≤ (0 : Int) + d2743 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3816, d2743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29569 p hg
    simpa only [d3816, d2743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3816, d2743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29577 p hg
    simpa only [d3816, d2743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29579 (p : Pattern) (guard : d5850 p = 1) : d3817 p ≤ (0 : Int) + d2744 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3817, d2744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29544 p hg
    simpa only [d3817, d2744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3817, d2744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29578 p hg
    simpa only [d3817, d2744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29580 (p : Pattern) (guard : d5850 p = 1) : d3818 p ≤ (0 : Int) + d2679 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3818, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29472 p hg
    simpa only [d5850, d3818, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3818, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29509 p hg
    simpa only [d5850, d3818, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29581 (p : Pattern) (guard : d5850 p = 1) : d3819 p ≤ (0 : Int) + d2680 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3819, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29510 p hg
    simpa only [d3819, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3819, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29580 p hg
    simpa only [d3819, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29582 (p : Pattern) (guard : d5850 p = 1) : d3820 p ≤ (0 : Int) + d2686 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3820, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29467 p hg
    simpa only [d3820, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3820, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29581 p hg
    simpa only [d3820, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29583 (p : Pattern) (guard : d5850 p = 1) : d3821 p ≤ (0 : Int) + d2745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3821, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29474 p hg
    simpa only [d3821, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3821, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3821, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29584 (p : Pattern) (guard : d5850 p = 1) : d3822 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3822, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29582 p hg
    simpa only [d3822, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3822, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29583 p hg
    simpa only [d3822, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29585 (p : Pattern) (guard : d0 p = 1) : d3823 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29586 (p : Pattern) (guard : d5850 p = 1) : d3824 p ≤ (0 : Int) + d2679 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3824, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29472 p hg
    simpa only [d5850, d3824, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3824, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29585 p hg
    simpa only [d5850, d3824, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29587 (p : Pattern) (guard : d5850 p = 1) : d3825 p ≤ (0 : Int) + d2680 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3825, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29510 p hg
    simpa only [d3825, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3825, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29586 p hg
    simpa only [d3825, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29588 (p : Pattern) (guard : d5850 p = 1) : d3826 p ≤ (0 : Int) + d2745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3826, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29587 p hg
    simpa only [d3826, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3826, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3826, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29589 (p : Pattern) (guard : d5850 p = 1) : d3827 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3827, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29513 p hg
    simpa only [d3827, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3827, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29588 p hg
    simpa only [d3827, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29590 (p : Pattern) (guard : d5850 p = 1) : d3828 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29584 p hg
    simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29589 p hg
    simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29591 (p : Pattern) (guard : d5850 p = 1) : d3829 p ≤ (0 : Int) + d2745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3829, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29512 p hg
    simpa only [d3829, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3829, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3829, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29592 (p : Pattern) (guard : d5850 p = 1) : d3830 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3830, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29513 p hg
    simpa only [d3830, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3830, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29591 p hg
    simpa only [d3830, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29593 (p : Pattern) (guard : d5850 p = 1) : d3831 p ≤ (0 : Int) + d2747 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3831, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29536 p hg
    simpa only [d3831, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3831, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3831, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29594 (p : Pattern) (guard : d5850 p = 1) : d3832 p ≤ (0 : Int) + d2748 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3832, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29537 p hg
    simpa only [d3832, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3832, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29593 p hg
    simpa only [d3832, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29595 (p : Pattern) (guard : d5850 p = 1) : d3833 p ≤ (0 : Int) + d2749 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3833, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29592 p hg
    simpa only [d3833, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3833, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29594 p hg
    simpa only [d3833, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29596 (p : Pattern) (guard : d5850 p = 1) : d3834 p ≤ (0 : Int) + d2750 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3834, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29590 p hg
    simpa only [d3834, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3834, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29595 p hg
    simpa only [d3834, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29597 (p : Pattern) (guard : d5850 p = 1) : d3835 p ≤ (0 : Int) + d2751 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3835, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29595 p hg
    simpa only [d3835, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3835, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29506 p hg
    simpa only [d3835, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29598 (p : Pattern) (guard : d5850 p = 1) : d3836 p ≤ (0 : Int) + d2752 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3836, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29596 p hg
    simpa only [d3836, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3836, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29597 p hg
    simpa only [d3836, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29599 (p : Pattern) (guard : d5850 p = 1) : d3837 p ≤ (0 : Int) + d2753 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3837, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29570 p hg
    simpa only [d3837, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3837, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29521 p hg
    simpa only [d3837, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29600 (p : Pattern) (guard : d5850 p = 1) : d119 p ≤ (0 : Int) + d2707 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29523 p hg
    simpa only [d5850, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5850, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29601 (p : Pattern) (guard : d5850 p = 1) : d3838 p ≤ (0 : Int) + d2754 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3838, d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29600 p hg
    simpa only [d3838, d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3838, d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29528 p hg
    simpa only [d3838, d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29602 (p : Pattern) (guard : d5850 p = 1) : d3839 p ≤ (0 : Int) + d2755 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3839, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29601 p hg
    simpa only [d3839, d2755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3839, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29529 p hg
    simpa only [d3839, d2755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29603 (p : Pattern) (guard : d5850 p = 1) : d3840 p ≤ (0 : Int) + d2756 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3840, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29599 p hg
    simpa only [d3840, d2756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3840, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29602 p hg
    simpa only [d3840, d2756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29604 (p : Pattern) (guard : d5850 p = 1) : d3841 p ≤ (0 : Int) + d2757 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3841, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29603 p hg
    simpa only [d3841, d2757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3841, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3841, d2757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29605 (p : Pattern) (guard : d5850 p = 1) : d3842 p ≤ (0 : Int) + d2758 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3842, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29604 p hg
    simpa only [d3842, d2758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3842, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3842, d2758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29606 (p : Pattern) (guard : d5850 p = 1) : d3843 p ≤ (0 : Int) + d2759 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3843, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29598 p hg
    simpa only [d3843, d2759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3843, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29605 p hg
    simpa only [d3843, d2759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29607 (p : Pattern) (guard : d5850 p = 1) : d3844 p ≤ (0 : Int) + d2760 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3844, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29589 p hg
    simpa only [d3844, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3844, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29599 p hg
    simpa only [d3844, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29608 (p : Pattern) (guard : d5850 p = 1) : d3845 p ≤ (0 : Int) + d2761 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3845, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29594 p hg
    simpa only [d3845, d2761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3845, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29348 p hg
    simpa only [d3845, d2761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29609 (p : Pattern) (guard : d5850 p = 1) : d3846 p ≤ (0 : Int) + d2762 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3846, d2762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29607 p hg
    simpa only [d3846, d2762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3846, d2762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29608 p hg
    simpa only [d3846, d2762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29610 (p : Pattern) (guard : d5850 p = 1) : d3847 p ≤ (0 : Int) + d2763 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3847, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29594 p hg
    simpa only [d3847, d2763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3847, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29352 p hg
    simpa only [d3847, d2763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29611 (p : Pattern) (guard : d5850 p = 1) : d3848 p ≤ (0 : Int) + d2764 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3848, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29610 p hg
    simpa only [d3848, d2764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3848, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3848, d2764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29612 (p : Pattern) (guard : d5850 p = 1) : d3849 p ≤ (0 : Int) + d2765 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3849, d2765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29609 p hg
    simpa only [d3849, d2765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3849, d2765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29611 p hg
    simpa only [d3849, d2765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29613 (p : Pattern) (guard : d5850 p = 1) : d3850 p ≤ (0 : Int) + d2766 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3850, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29602 p hg
    simpa only [d3850, d2766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3850, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3850, d2766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29614 (p : Pattern) (guard : d5850 p = 1) : d3851 p ≤ (0 : Int) + d2767 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3851, d2767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29613 p hg
    simpa only [d3851, d2767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3851, d2767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3851, d2767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29615 (p : Pattern) (guard : d5850 p = 1) : d3852 p ≤ (0 : Int) + d2768 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3852, d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29614 p hg
    simpa only [d3852, d2768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3852, d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3852, d2768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29616 (p : Pattern) (guard : d5850 p = 1) : d3853 p ≤ (0 : Int) + d2769 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3853, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29612 p hg
    simpa only [d3853, d2769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3853, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29615 p hg
    simpa only [d3853, d2769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29617 (p : Pattern) (guard : d5850 p = 1) : d3854 p ≤ (0 : Int) + d2770 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3854, d2770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29606 p hg
    simpa only [d3854, d2770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3854, d2770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29616 p hg
    simpa only [d3854, d2770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29618 (p : Pattern) (guard : d5850 p = 1) : d3855 p ≤ (0 : Int) + d2771 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3855, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29579 p hg
    simpa only [d3855, d2771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3855, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29617 p hg
    simpa only [d3855, d2771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29619 (p : Pattern) (guard : d5850 p = 1) : d3856 p ≤ (0 : Int) + d2772 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3856, d2772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29506 p hg
    simpa only [d3856, d2772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3856, d2772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3856, d2772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29620 (p : Pattern) (guard : d5850 p = 1) : d3857 p ≤ (0 : Int) + d2773 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3857, d2773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29619 p hg
    simpa only [d3857, d2773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3857, d2773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3857, d2773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29621 (p : Pattern) (guard : d5850 p = 1) : d3858 p ≤ (0 : Int) + d2774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3858, d2774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29620 p hg
    simpa only [d3858, d2774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3858, d2774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3858, d2774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29622 (p : Pattern) (guard : d5850 p = 1) : d3859 p ≤ (0 : Int) + d2775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3859, d2775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29621 p hg
    simpa only [d3859, d2775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3859, d2775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3859, d2775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29623 (p : Pattern) (guard : d5850 p = 1) : d3860 p ≤ (0 : Int) + d2776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3860, d2776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29617 p hg
    simpa only [d3860, d2776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3860, d2776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29622 p hg
    simpa only [d3860, d2776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29624 (p : Pattern) (guard : d5850 p = 1) : d3861 p ≤ (0 : Int) + d2777 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3861, d2777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29618 p hg
    simpa only [d3861, d2777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3861, d2777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29623 p hg
    simpa only [d3861, d2777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29625 (p : Pattern) (guard : d5850 p = 1) : d3862 p ≤ (0 : Int) + d2778 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3862, d2778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29485 p hg
    simpa only [d3862, d2778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3862, d2778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29504 p hg
    simpa only [d3862, d2778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29626 (p : Pattern) (guard : d5850 p = 1) : d3863 p ≤ (0 : Int) + d2779 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3863, d2779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29625 p hg
    simpa only [d3863, d2779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3863, d2779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29507 p hg
    simpa only [d3863, d2779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29627 (p : Pattern) (guard : d5850 p = 1) : d3864 p ≤ (0 : Int) + d2780 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3864, d2780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29626 p hg
    simpa only [d3864, d2780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3864, d2780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29543 p hg
    simpa only [d3864, d2780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29628 (p : Pattern) (guard : d5850 p = 1) : d3802 p ≤ (0 : Int) + d2781 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3802, d2781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29485 p hg
    simpa only [d3802, d2781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3802, d2781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29563 p hg
    simpa only [d3802, d2781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29629 (p : Pattern) (guard : d5850 p = 1) : d3804 p ≤ (0 : Int) + d2782 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3804, d2782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29628 p hg
    simpa only [d3804, d2782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3804, d2782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29565 p hg
    simpa only [d3804, d2782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29630 (p : Pattern) (guard : d5850 p = 1) : d3807 p ≤ (0 : Int) + d2783 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3807, d2783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29629 p hg
    simpa only [d3807, d2783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3807, d2783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29568 p hg
    simpa only [d3807, d2783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29631 (p : Pattern) (guard : d5850 p = 1) : d3816 p ≤ (0 : Int) + d2784 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3816, d2784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29630 p hg
    simpa only [d3816, d2784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3816, d2784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29577 p hg
    simpa only [d3816, d2784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29632 (p : Pattern) (guard : d5850 p = 1) : d3865 p ≤ (0 : Int) + d2785 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3865, d2785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29627 p hg
    simpa only [d3865, d2785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3865, d2785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29631 p hg
    simpa only [d3865, d2785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29633 (p : Pattern) (guard : d5850 p = 1) : d3866 p ≤ (0 : Int) + d2786 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3866, d2786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29632 p hg
    simpa only [d3866, d2786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3866, d2786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29617 p hg
    simpa only [d3866, d2786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29634 (p : Pattern) (guard : d5850 p = 1) : d3867 p ≤ (0 : Int) + d2787 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3867, d2787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29617 p hg
    simpa only [d3867, d2787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3867, d2787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3867, d2787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29635 (p : Pattern) (guard : d5850 p = 1) : d3868 p ≤ (0 : Int) + d2788 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3868, d2788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29633 p hg
    simpa only [d3868, d2788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3868, d2788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29634 p hg
    simpa only [d3868, d2788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29636 (p : Pattern) (guard : d5850 p = 1) : d3869 p ≤ (0 : Int) + d2789 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3869, d2789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29624 p hg
    simpa only [d3869, d2789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3869, d2789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29635 p hg
    simpa only [d3869, d2789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29637 (p : Pattern) (guard : d5850 p = 1) : d3870 p ≤ (0 : Int) + d2790 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3870, d2790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29433 p hg
    simpa only [d3870, d2790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3870, d2790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29636 p hg
    simpa only [d3870, d2790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29638 (p : Pattern) (guard : d5850 p = 1) : d3871 p ≤ (0 : Int) + d2791 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3871, d2791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29460 p hg
    simpa only [d3871, d2791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3871, d2791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29637 p hg
    simpa only [d3871, d2791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29639 (p : Pattern) (guard : d5850 p = 1) : d3872 p ≤ (0 : Int) + d2521 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3872, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29240 p hg
    simpa only [d5850, d3872, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3872, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29301 p hg
    simpa only [d5850, d3872, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29640 (p : Pattern) (guard : d5850 p = 1) : d3873 p ≤ (0 : Int) + d2522 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3873, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29302 p hg
    simpa only [d3873, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3873, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29639 p hg
    simpa only [d3873, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29641 (p : Pattern) (guard : d5850 p = 1) : d3874 p ≤ (0 : Int) + d2523 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3874, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29236 p hg
    simpa only [d3874, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3874, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29640 p hg
    simpa only [d3874, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29642 (p : Pattern) (guard : d5850 p = 1) : d3875 p ≤ (0 : Int) + d2602 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3875, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29242 p hg
    simpa only [d3875, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3875, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3875, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29643 (p : Pattern) (guard : d5850 p = 1) : d3876 p ≤ (0 : Int) + d2603 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3876, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29641 p hg
    simpa only [d3876, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3876, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29642 p hg
    simpa only [d3876, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29644 (p : Pattern) (guard : d5850 p = 1) : d3877 p ≤ (0 : Int) + d2604 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3877, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29373 p hg
    simpa only [d3877, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3877, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29643 p hg
    simpa only [d3877, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29645 (p : Pattern) (guard : d5850 p = 1) : d3878 p ≤ (0 : Int) + d2605 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3878, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29373 p hg
    simpa only [d3878, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3878, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29644 p hg
    simpa only [d3878, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29646 (p : Pattern) (guard : d5850 p = 1) : d3879 p ≤ (0 : Int) + d2609 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3879, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29644 p hg
    simpa only [d3879, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3879, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29388 p hg
    simpa only [d3879, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29647 (p : Pattern) (guard : d5850 p = 1) : d3880 p ≤ (0 : Int) + d2610 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3880, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29645 p hg
    simpa only [d3880, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3880, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29646 p hg
    simpa only [d3880, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29648 (p : Pattern) (guard : d5850 p = 1) : d3881 p ≤ (0 : Int) + d2792 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3881, d2792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29356 p hg
    simpa only [d3881, d2792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3881, d2792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29292 p hg
    simpa only [d3881, d2792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29649 (p : Pattern) (guard : d5850 p = 1) : d3882 p ≤ (0 : Int) + d2793 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3882, d2793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29391 p hg
    simpa only [d3882, d2793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3882, d2793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29648 p hg
    simpa only [d3882, d2793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29650 (p : Pattern) (guard : d5850 p = 1) : d3883 p ≤ (0 : Int) + d2794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3883, d2794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29356 p hg
    simpa only [d3883, d2794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3883, d2794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29299 p hg
    simpa only [d3883, d2794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29651 (p : Pattern) (guard : d5850 p = 1) : d3884 p ≤ (0 : Int) + d2795 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3884, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29393 p hg
    simpa only [d3884, d2795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3884, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3884, d2795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29652 (p : Pattern) (guard : d5850 p = 1) : d3885 p ≤ (0 : Int) + d2796 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3885, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29650 p hg
    simpa only [d3885, d2796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3885, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29651 p hg
    simpa only [d3885, d2796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29653 (p : Pattern) (guard : d5850 p = 1) : d3886 p ≤ (0 : Int) + d2797 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3886, d2797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29649 p hg
    simpa only [d3886, d2797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3886, d2797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29652 p hg
    simpa only [d3886, d2797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29654 (p : Pattern) (guard : d5850 p = 1) : d3887 p ≤ (0 : Int) + d2798 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3887, d2798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29357 p hg
    simpa only [d3887, d2798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3887, d2798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29651 p hg
    simpa only [d3887, d2798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29655 (p : Pattern) (guard : d5850 p = 1) : d3888 p ≤ (0 : Int) + d2799 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3888, d2799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29654 p hg
    simpa only [d3888, d2799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3888, d2799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29364 p hg
    simpa only [d3888, d2799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29656 (p : Pattern) (guard : d5850 p = 1) : d3889 p ≤ (0 : Int) + d2800 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3889, d2800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29653 p hg
    simpa only [d3889, d2800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3889, d2800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29655 p hg
    simpa only [d3889, d2800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29657 (p : Pattern) (guard : d5850 p = 1) : d3890 p ≤ (0 : Int) + d2801 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3890, d2801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29647 p hg
    simpa only [d3890, d2801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3890, d2801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29656 p hg
    simpa only [d3890, d2801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29658 (p : Pattern) (guard : d5850 p = 1) : d3891 p ≤ (0 : Int) + d2541 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3891, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29281 p hg
    simpa only [d5850, d3891, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3891, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29278 p hg
    simpa only [d5850, d3891, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29659 (p : Pattern) (guard : d5850 p = 1) : d3892 p ≤ (0 : Int) + d2542 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3892, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29279 p hg
    simpa only [d3892, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3892, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29658 p hg
    simpa only [d3892, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29660 (p : Pattern) (guard : d5850 p = 1) : d3893 p ≤ (0 : Int) + d2569 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3893, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29324 p hg
    simpa only [d3893, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3893, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29659 p hg
    simpa only [d3893, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29661 (p : Pattern) (guard : d5850 p = 1) : d3894 p ≤ (0 : Int) + d2543 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3894, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29328 p hg
    simpa only [d3894, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3894, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3894, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29662 (p : Pattern) (guard : d5850 p = 1) : d3895 p ≤ (0 : Int) + d2611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3895, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29660 p hg
    simpa only [d3895, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3895, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29661 p hg
    simpa only [d3895, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29663 (p : Pattern) (guard : d5850 p = 1) : d3896 p ≤ (0 : Int) + d2618 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3896, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29373 p hg
    simpa only [d3896, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3896, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29662 p hg
    simpa only [d3896, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29664 (p : Pattern) (guard : d5850 p = 1) : d3897 p ≤ (0 : Int) + d2619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3897, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29643 p hg
    simpa only [d3897, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3897, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29387 p hg
    simpa only [d3897, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29665 (p : Pattern) (guard : d5850 p = 1) : d3898 p ≤ (0 : Int) + d2620 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3898, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29663 p hg
    simpa only [d3898, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3898, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29664 p hg
    simpa only [d3898, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29666 (p : Pattern) (guard : d5850 p = 1) : d3899 p ≤ (0 : Int) + d2621 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3899, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29643 p hg
    simpa only [d3899, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3899, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29348 p hg
    simpa only [d3899, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29667 (p : Pattern) (guard : d5850 p = 1) : d3900 p ≤ (0 : Int) + d2622 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3900, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29666 p hg
    simpa only [d3900, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3900, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29353 p hg
    simpa only [d3900, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29668 (p : Pattern) (guard : d5850 p = 1) : d3901 p ≤ (0 : Int) + d2623 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3901, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29665 p hg
    simpa only [d3901, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3901, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29667 p hg
    simpa only [d3901, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29669 (p : Pattern) (guard : d5850 p = 1) : d3902 p ≤ (0 : Int) + d2802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3902, d2802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29648 p hg
    simpa only [d3902, d2802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3902, d2802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29306 p hg
    simpa only [d3902, d2802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29670 (p : Pattern) (guard : d5850 p = 1) : d3903 p ≤ (0 : Int) + d2803 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3903, d2803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29651 p hg
    simpa only [d3903, d2803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3903, d2803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29363 p hg
    simpa only [d3903, d2803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29671 (p : Pattern) (guard : d5850 p = 1) : d3904 p ≤ (0 : Int) + d2804 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3904, d2804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29669 p hg
    simpa only [d3904, d2804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3904, d2804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29670 p hg
    simpa only [d3904, d2804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29672 (p : Pattern) (guard : d5850 p = 1) : d3905 p ≤ (0 : Int) + d2805 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3905, d2805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29651 p hg
    simpa only [d3905, d2805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3905, d2805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3905, d2805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29673 (p : Pattern) (guard : d5850 p = 1) : d3906 p ≤ (0 : Int) + d2806 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3906, d2806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29672 p hg
    simpa only [d3906, d2806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3906, d2806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3906, d2806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29674 (p : Pattern) (guard : d5850 p = 1) : d3907 p ≤ (0 : Int) + d2807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3907, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29671 p hg
    simpa only [d3907, d2807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3907, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29673 p hg
    simpa only [d3907, d2807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29675 (p : Pattern) (guard : d5850 p = 1) : d3908 p ≤ (0 : Int) + d2808 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3908, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29668 p hg
    simpa only [d3908, d2808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3908, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29674 p hg
    simpa only [d3908, d2808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29676 (p : Pattern) (guard : d5850 p = 1) : d3909 p ≤ (0 : Int) + d2809 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3909, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29657 p hg
    simpa only [d3909, d2809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3909, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29675 p hg
    simpa only [d3909, d2809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29677 (p : Pattern) (guard : d5850 p = 1) : d3910 p ≤ (0 : Int) + d2518 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3910, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29210 p hg
    simpa only [d3910, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3910, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29376 p hg
    simpa only [d3910, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29678 (p : Pattern) (guard : d5850 p = 1) : d3911 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3911, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29370 p hg
    simpa only [d3911, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3911, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3911, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29679 (p : Pattern) (guard : d5850 p = 1) : d3912 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3912, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29677 p hg
    simpa only [d3912, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3912, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29678 p hg
    simpa only [d3912, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
