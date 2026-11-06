/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons147
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare20720 (p : Pattern) (guard : d5850 p = 1) : d2648 p ≤ (0 : Int) + d3714 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2648, d3714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20715 p hg
    simpa only [d2648, d3714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2648, d3714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20719 p hg
    simpa only [d2648, d3714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20721 (p : Pattern) (guard : d5850 p = 1) : d2649 p ≤ (0 : Int) + d3715 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2649, d3715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20720 p hg
    simpa only [d2649, d3715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2649, d3715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20700 p hg
    simpa only [d2649, d3715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20722 (p : Pattern) (guard : d5850 p = 1) : d2650 p ≤ (0 : Int) + d3716 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2650, d3716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20700 p hg
    simpa only [d2650, d3716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2650, d3716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2650, d3716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20723 (p : Pattern) (guard : d5850 p = 1) : d2651 p ≤ (0 : Int) + d3717 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2651, d3717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20721 p hg
    simpa only [d2651, d3717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2651, d3717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20722 p hg
    simpa only [d2651, d3717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20724 (p : Pattern) (guard : d5850 p = 1) : d2652 p ≤ (0 : Int) + d3718 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2652, d3718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20711 p hg
    simpa only [d2652, d3718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2652, d3718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20723 p hg
    simpa only [d2652, d3718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20725 (p : Pattern) (guard : d0 p = 1) : d356 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20726 (p : Pattern) (guard : d5850 p = 1) : d2653 p ≤ (0 : Int) + d3720 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2653, d3720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20103 p hg
    simpa only [d5850, d2653, d3720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2653, d3720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20725 p hg
    simpa only [d5850, d2653, d3720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20727 (p : Pattern) (guard : d5850 p = 1) : d2654 p ≤ (0 : Int) + d3721 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2654, d3721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20726 p hg
    simpa only [d2654, d3721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2654, d3721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20510 p hg
    simpa only [d2654, d3721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20728 (p : Pattern) (guard : d5850 p = 1) : d2655 p ≤ (0 : Int) + d3722 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2655, d3722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20727 p hg
    simpa only [d2655, d3722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2655, d3722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20516 p hg
    simpa only [d2655, d3722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20729 (p : Pattern) (guard : d5850 p = 1) : d2656 p ≤ (0 : Int) + d3723 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2656, d3723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20728 p hg
    simpa only [d2656, d3723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2656, d3723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20524 p hg
    simpa only [d2656, d3723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20730 (p : Pattern) (guard : d5850 p = 1) : d2657 p ≤ (0 : Int) + d3724 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2657, d3724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20729 p hg
    simpa only [d2657, d3724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2657, d3724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20533 p hg
    simpa only [d2657, d3724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20731 (p : Pattern) (guard : d5850 p = 1) : d2658 p ≤ (0 : Int) + d3725 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2658, d3725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20730 p hg
    simpa only [d2658, d3725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2658, d3725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20548 p hg
    simpa only [d2658, d3725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20732 (p : Pattern) (guard : d5850 p = 1) : d2659 p ≤ (0 : Int) + d3726 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2659, d3726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20731 p hg
    simpa only [d2659, d3726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2659, d3726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20564 p hg
    simpa only [d2659, d3726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20733 (p : Pattern) (guard : d5850 p = 1) : d2660 p ≤ (0 : Int) + d3727 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2660, d3727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20732 p hg
    simpa only [d2660, d3727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2660, d3727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20610 p hg
    simpa only [d2660, d3727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20734 (p : Pattern) (guard : d5850 p = 1) : d2661 p ≤ (0 : Int) + d3710 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2661, d3710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20530 p hg
    simpa only [d2661, d3710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2661, d3710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20628 p hg
    simpa only [d2661, d3710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20735 (p : Pattern) (guard : d5850 p = 1) : d2662 p ≤ (0 : Int) + d3711 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2662, d3711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20734 p hg
    simpa only [d2662, d3711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2662, d3711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20630 p hg
    simpa only [d2662, d3711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20736 (p : Pattern) (guard : d5850 p = 1) : d2663 p ≤ (0 : Int) + d3712 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2663, d3712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20735 p hg
    simpa only [d2663, d3712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2663, d3712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20645 p hg
    simpa only [d2663, d3712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20737 (p : Pattern) (guard : d5850 p = 1) : d2664 p ≤ (0 : Int) + d3713 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2664, d3713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20736 p hg
    simpa only [d2664, d3713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2664, d3713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20657 p hg
    simpa only [d2664, d3713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20738 (p : Pattern) (guard : d5850 p = 1) : d2665 p ≤ (0 : Int) + d3728 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2665, d3728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20733 p hg
    simpa only [d2665, d3728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2665, d3728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20737 p hg
    simpa only [d2665, d3728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20739 (p : Pattern) (guard : d5850 p = 1) : d2666 p ≤ (0 : Int) + d3729 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2666, d3729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20738 p hg
    simpa only [d2666, d3729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2666, d3729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20700 p hg
    simpa only [d2666, d3729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20740 (p : Pattern) (guard : d5850 p = 1) : d2667 p ≤ (0 : Int) + d3730 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2667, d3730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20739 p hg
    simpa only [d2667, d3730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2667, d3730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20710 p hg
    simpa only [d2667, d3730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20741 (p : Pattern) (guard : d5850 p = 1) : d2668 p ≤ (0 : Int) + d3707 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2668, d3707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20533 p hg
    simpa only [d2668, d3707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2668, d3707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20548 p hg
    simpa only [d2668, d3707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20742 (p : Pattern) (guard : d5850 p = 1) : d2669 p ≤ (0 : Int) + d3708 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2669, d3708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20741 p hg
    simpa only [d2669, d3708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2669, d3708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20564 p hg
    simpa only [d2669, d3708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20743 (p : Pattern) (guard : d5850 p = 1) : d2670 p ≤ (0 : Int) + d3709 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2670, d3709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20742 p hg
    simpa only [d2670, d3709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2670, d3709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20610 p hg
    simpa only [d2670, d3709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20744 (p : Pattern) (guard : d5850 p = 1) : d2671 p ≤ (0 : Int) + d3714 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2671, d3714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20743 p hg
    simpa only [d2671, d3714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2671, d3714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20719 p hg
    simpa only [d2671, d3714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20745 (p : Pattern) (guard : d5850 p = 1) : d2672 p ≤ (0 : Int) + d3715 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2672, d3715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20744 p hg
    simpa only [d2672, d3715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2672, d3715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20700 p hg
    simpa only [d2672, d3715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20746 (p : Pattern) (guard : d5850 p = 1) : d2673 p ≤ (0 : Int) + d3717 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2673, d3717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20745 p hg
    simpa only [d2673, d3717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2673, d3717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20722 p hg
    simpa only [d2673, d3717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20747 (p : Pattern) (guard : d5850 p = 1) : d2674 p ≤ (0 : Int) + d3731 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2674, d3731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20740 p hg
    simpa only [d2674, d3731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2674, d3731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20746 p hg
    simpa only [d2674, d3731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20748 (p : Pattern) (guard : d5850 p = 1) : d2675 p ≤ (0 : Int) + d3732 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2675, d3732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20724 p hg
    simpa only [d2675, d3732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2675, d3732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20747 p hg
    simpa only [d2675, d3732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20749 (p : Pattern) (guard : d0 p = 1) : d356 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20750 (p : Pattern) (guard : d5850 p = 1) : d2676 p ≤ (0 : Int) + d3734 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2676, d3734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20133 p hg
    simpa only [d5850, d2676, d3734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2676, d3734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20749 p hg
    simpa only [d5850, d2676, d3734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20751 (p : Pattern) (guard : d5850 p = 1) : d2677 p ≤ (0 : Int) + d102 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d5850, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20160 p hg
    simpa only [d5850, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20752 (p : Pattern) (guard : d5850 p = 1) : d2678 p ≤ (0 : Int) + d3735 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2678, d3735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20750 p hg
    simpa only [d2678, d3735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2678, d3735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20751 p hg
    simpa only [d2678, d3735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20753 (p : Pattern) (guard : d5850 p = 1) : d2677 p ≤ (0 : Int) + d3737 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2677, d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d5850, d2677, d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2677, d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20144 p hg
    simpa only [d5850, d2677, d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20754 (p : Pattern) (guard : d5843 p = 1) : d1939 p ≤ (0 : Int) + d102 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1939, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d1939, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1939, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20164 p hg
    simpa only [d5843, d1939, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20755 (p : Pattern) (guard : d5843 p = 1) : d1940 p ≤ (0 : Int) + d3736 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1940, d3736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20754 p hg
    simpa only [d1940, d3736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1940, d3736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20166 p hg
    simpa only [d1940, d3736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20756 (p : Pattern) (guard : d5850 p = 1) : d2679 p ≤ (0 : Int) + d3736 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20755 p hg
    simpa only [d5850, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20144 p hg
    simpa only [d5850, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20757 (p : Pattern) (guard : d5850 p = 1) : d2680 p ≤ (0 : Int) + d3738 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2680, d3738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20753 p hg
    simpa only [d2680, d3738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2680, d3738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20756 p hg
    simpa only [d2680, d3738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20758 (p : Pattern) (guard : d5850 p = 1) : d2681 p ≤ (0 : Int) + d3739 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2681, d3739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20752 p hg
    simpa only [d2681, d3739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2681, d3739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20757 p hg
    simpa only [d2681, d3739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20759 (p : Pattern) (guard : d5850 p = 1) : d2677 p ≤ (0 : Int) + d3741 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2677, d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d5850, d2677, d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2677, d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20150 p hg
    simpa only [d5850, d2677, d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20760 (p : Pattern) (guard : d5843 p = 1) : d1872 p ≤ (0 : Int) + d102 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1872, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d1872, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1872, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20196 p hg
    simpa only [d5843, d1872, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20761 (p : Pattern) (guard : d5843 p = 1) : d1873 p ≤ (0 : Int) + d3740 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1873, d3740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20760 p hg
    simpa only [d1873, d3740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1873, d3740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20198 p hg
    simpa only [d1873, d3740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20762 (p : Pattern) (guard : d5850 p = 1) : d2682 p ≤ (0 : Int) + d3740 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20761 p hg
    simpa only [d5850, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20150 p hg
    simpa only [d5850, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20763 (p : Pattern) (guard : d5850 p = 1) : d2683 p ≤ (0 : Int) + d3742 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2683, d3742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20759 p hg
    simpa only [d2683, d3742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2683, d3742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20762 p hg
    simpa only [d2683, d3742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20764 (p : Pattern) (guard : d5850 p = 1) : d2684 p ≤ (0 : Int) + d3743 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2684, d3743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20763 p hg
    simpa only [d2684, d3743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2684, d3743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2684, d3743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20765 (p : Pattern) (guard : d5850 p = 1) : d2685 p ≤ (0 : Int) + d3744 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2685, d3744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20758 p hg
    simpa only [d2685, d3744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2685, d3744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20764 p hg
    simpa only [d2685, d3744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20766 (p : Pattern) (guard : d5850 p = 1) : d2686 p ≤ (0 : Int) + d3745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2686, d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20751 p hg
    simpa only [d2686, d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2686, d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20757 p hg
    simpa only [d2686, d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20767 (p : Pattern) (guard : d5850 p = 1) : d2687 p ≤ (0 : Int) + d3746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2687, d3746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20766 p hg
    simpa only [d2687, d3746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2687, d3746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20764 p hg
    simpa only [d2687, d3746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20768 (p : Pattern) (guard : d5850 p = 1) : d2688 p ≤ (0 : Int) + d3747 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2688, d3747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20765 p hg
    simpa only [d2688, d3747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2688, d3747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20767 p hg
    simpa only [d2688, d3747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20769 (p : Pattern) (guard : d5850 p = 1) : d2689 p ≤ (0 : Int) + d106 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20167 p hg
    simpa only [d5850, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20170 p hg
    simpa only [d5850, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20770 (p : Pattern) (guard : d5850 p = 1) : d2689 p ≤ (0 : Int) + d3749 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2689, d3749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20167 p hg
    simpa only [d5850, d2689, d3749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2689, d3749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20175 p hg
    simpa only [d5850, d2689, d3749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20771 (p : Pattern) (guard : d5843 p = 1) : d1963 p ≤ (0 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1963, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14654 p hg
    simpa only [d5843, d1963, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1963, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19887 p hg
    simpa only [d5843, d1963, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20772 (p : Pattern) (guard : d5843 p = 1) : d1964 p ≤ (0 : Int) + d3748 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1964, d3748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20771 p hg
    simpa only [d1964, d3748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1964, d3748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19889 p hg
    simpa only [d1964, d3748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20773 (p : Pattern) (guard : d5850 p = 1) : d2690 p ≤ (0 : Int) + d3748 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20772 p hg
    simpa only [d5850, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20175 p hg
    simpa only [d5850, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20774 (p : Pattern) (guard : d5850 p = 1) : d2691 p ≤ (0 : Int) + d3750 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2691, d3750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20770 p hg
    simpa only [d2691, d3750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2691, d3750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20773 p hg
    simpa only [d2691, d3750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20775 (p : Pattern) (guard : d5850 p = 1) : d2692 p ≤ (0 : Int) + d3751 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2692, d3751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20769 p hg
    simpa only [d2692, d3751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2692, d3751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20774 p hg
    simpa only [d2692, d3751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20776 (p : Pattern) (guard : d5850 p = 1) : d2689 p ≤ (0 : Int) + d3753 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2689, d3753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20167 p hg
    simpa only [d5850, d2689, d3753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2689, d3753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20181 p hg
    simpa only [d5850, d2689, d3753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20777 (p : Pattern) (guard : d5843 p = 1) : d1880 p ≤ (0 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1880, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14654 p hg
    simpa only [d5843, d1880, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1880, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20207 p hg
    simpa only [d5843, d1880, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20778 (p : Pattern) (guard : d5843 p = 1) : d1881 p ≤ (0 : Int) + d3752 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1881, d3752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20777 p hg
    simpa only [d1881, d3752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1881, d3752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20209 p hg
    simpa only [d1881, d3752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20779 (p : Pattern) (guard : d5850 p = 1) : d2693 p ≤ (0 : Int) + d3752 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20778 p hg
    simpa only [d5850, d2693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20181 p hg
    simpa only [d5850, d2693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20780 (p : Pattern) (guard : d5850 p = 1) : d2694 p ≤ (0 : Int) + d3754 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2694, d3754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20776 p hg
    simpa only [d2694, d3754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2694, d3754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20779 p hg
    simpa only [d2694, d3754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20781 (p : Pattern) (guard : d5850 p = 1) : d2695 p ≤ (0 : Int) + d3755 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2695, d3755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20780 p hg
    simpa only [d2695, d3755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2695, d3755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2695, d3755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20782 (p : Pattern) (guard : d5850 p = 1) : d2696 p ≤ (0 : Int) + d3756 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2696, d3756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20775 p hg
    simpa only [d2696, d3756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2696, d3756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20781 p hg
    simpa only [d2696, d3756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20783 (p : Pattern) (guard : d5850 p = 1) : d2697 p ≤ (0 : Int) + d3757 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2697, d3757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20767 p hg
    simpa only [d2697, d3757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2697, d3757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20782 p hg
    simpa only [d2697, d3757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20784 (p : Pattern) (guard : d5850 p = 1) : d2698 p ≤ (0 : Int) + d3758 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2698, d3758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20768 p hg
    simpa only [d2698, d3758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2698, d3758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20783 p hg
    simpa only [d2698, d3758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20785 (p : Pattern) (guard : d5850 p = 1) : d2699 p ≤ (0 : Int) + d3759 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2699, d3759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20639 p hg
    simpa only [d2699, d3759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2699, d3759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2699, d3759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20786 (p : Pattern) (guard : d5850 p = 1) : d2700 p ≤ (0 : Int) + d3760 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2700, d3760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20783 p hg
    simpa only [d2700, d3760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2700, d3760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20785 p hg
    simpa only [d2700, d3760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20787 (p : Pattern) (guard : d5850 p = 1) : d2701 p ≤ (0 : Int) + d3761 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2701, d3761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20784 p hg
    simpa only [d2701, d3761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2701, d3761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20786 p hg
    simpa only [d2701, d3761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20788 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3762 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20789 (p : Pattern) (guard : d5850 p = 1) : d2677 p ≤ (0 : Int) + d3763 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2677, d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d5850, d2677, d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2677, d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20788 p hg
    simpa only [d5850, d2677, d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20790 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1955 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20791 (p : Pattern) (guard : d5850 p = 1) : d2679 p ≤ (0 : Int) + d3764 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2679, d3764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20755 p hg
    simpa only [d5850, d2679, d3764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2679, d3764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20790 p hg
    simpa only [d5850, d2679, d3764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20792 (p : Pattern) (guard : d5850 p = 1) : d2680 p ≤ (0 : Int) + d3765 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2680, d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20789 p hg
    simpa only [d2680, d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2680, d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20791 p hg
    simpa only [d2680, d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20793 (p : Pattern) (guard : d5850 p = 1) : d2686 p ≤ (0 : Int) + d3766 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2686, d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20751 p hg
    simpa only [d2686, d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2686, d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20792 p hg
    simpa only [d2686, d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20794 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20795 (p : Pattern) (guard : d5850 p = 1) : d2702 p ≤ (0 : Int) + d3768 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2702, d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20199 p hg
    simpa only [d5850, d2702, d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2702, d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20794 p hg
    simpa only [d5850, d2702, d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20796 (p : Pattern) (guard : d5843 p = 1) : d1894 p ≤ (0 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1894, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d5843, d1894, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1894, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20207 p hg
    simpa only [d5843, d1894, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20797 (p : Pattern) (guard : d5843 p = 1) : d1895 p ≤ (0 : Int) + d3769 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1895, d3769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20796 p hg
    simpa only [d1895, d3769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1895, d3769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20209 p hg
    simpa only [d1895, d3769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20798 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1896 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20799 (p : Pattern) (guard : d5850 p = 1) : d2703 p ≤ (0 : Int) + d3770 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2703, d3770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20797 p hg
    simpa only [d5850, d2703, d3770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2703, d3770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20798 p hg
    simpa only [d5850, d2703, d3770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20800 (p : Pattern) (guard : d5850 p = 1) : d2704 p ≤ (0 : Int) + d3771 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2704, d3771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20795 p hg
    simpa only [d2704, d3771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2704, d3771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20799 p hg
    simpa only [d2704, d3771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20801 (p : Pattern) (guard : d5850 p = 1) : d2705 p ≤ (0 : Int) + d3772 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2705, d3772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20800 p hg
    simpa only [d2705, d3772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2705, d3772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2705, d3772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20802 (p : Pattern) (guard : d5850 p = 1) : d2706 p ≤ (0 : Int) + d3773 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2706, d3773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20793 p hg
    simpa only [d2706, d3773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2706, d3773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20801 p hg
    simpa only [d2706, d3773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20803 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d317 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20804 (p : Pattern) (guard : d5850 p = 1) : d2707 p ≤ (0 : Int) + d3774 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2707, d3774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20210 p hg
    simpa only [d5850, d2707, d3774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2707, d3774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20803 p hg
    simpa only [d5850, d2707, d3774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20805 (p : Pattern) (guard : d5843 p = 1) : d1902 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1902, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14675 p hg
    simpa only [d5843, d1902, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1902, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19937 p hg
    simpa only [d5843, d1902, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20806 (p : Pattern) (guard : d5843 p = 1) : d1903 p ≤ (0 : Int) + d3775 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1903, d3775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20805 p hg
    simpa only [d1903, d3775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1903, d3775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19939 p hg
    simpa only [d1903, d3775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20807 (p : Pattern) (guard : d5850 p = 1) : d2708 p ≤ (0 : Int) + d3776 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2708, d3776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20806 p hg
    simpa only [d5850, d2708, d3776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2708, d3776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20803 p hg
    simpa only [d5850, d2708, d3776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20808 (p : Pattern) (guard : d5850 p = 1) : d2709 p ≤ (0 : Int) + d3777 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2709, d3777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20804 p hg
    simpa only [d2709, d3777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2709, d3777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20807 p hg
    simpa only [d2709, d3777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20809 (p : Pattern) (guard : d5850 p = 1) : d2710 p ≤ (0 : Int) + d3778 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2710, d3778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20808 p hg
    simpa only [d2710, d3778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2710, d3778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2710, d3778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20810 (p : Pattern) (guard : d5850 p = 1) : d2711 p ≤ (0 : Int) + d3779 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2711, d3779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20793 p hg
    simpa only [d2711, d3779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2711, d3779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20809 p hg
    simpa only [d2711, d3779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20811 (p : Pattern) (guard : d5850 p = 1) : d2712 p ≤ (0 : Int) + d3780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2712, d3780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20802 p hg
    simpa only [d2712, d3780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2712, d3780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20810 p hg
    simpa only [d2712, d3780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20812 (p : Pattern) (guard : d5850 p = 1) : d2713 p ≤ (0 : Int) + d3781 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2713, d3781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20793 p hg
    simpa only [d2713, d3781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2713, d3781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2713, d3781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20813 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20814 (p : Pattern) (guard : d5850 p = 1) : d2689 p ≤ (0 : Int) + d3783 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2689, d3783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20167 p hg
    simpa only [d5850, d2689, d3783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2689, d3783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20813 p hg
    simpa only [d5850, d2689, d3783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20815 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d348 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20816 (p : Pattern) (guard : d5850 p = 1) : d2690 p ≤ (0 : Int) + d3784 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2690, d3784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20772 p hg
    simpa only [d5850, d2690, d3784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2690, d3784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20815 p hg
    simpa only [d5850, d2690, d3784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20817 (p : Pattern) (guard : d5850 p = 1) : d2691 p ≤ (0 : Int) + d3785 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2691, d3785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20814 p hg
    simpa only [d2691, d3785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2691, d3785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20816 p hg
    simpa only [d2691, d3785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20818 (p : Pattern) (guard : d5850 p = 1) : d2692 p ≤ (0 : Int) + d3786 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2692, d3786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20769 p hg
    simpa only [d2692, d3786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2692, d3786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20817 p hg
    simpa only [d2692, d3786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20819 (p : Pattern) (guard : d5850 p = 1) : d2714 p ≤ (0 : Int) + d3787 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2714, d3787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20818 p hg
    simpa only [d2714, d3787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2714, d3787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2714, d3787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20820 (p : Pattern) (guard : d5850 p = 1) : d2715 p ≤ (0 : Int) + d3788 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2715, d3788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20812 p hg
    simpa only [d2715, d3788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2715, d3788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20819 p hg
    simpa only [d2715, d3788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20821 (p : Pattern) (guard : d5850 p = 1) : d2716 p ≤ (0 : Int) + d3789 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2716, d3789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20811 p hg
    simpa only [d2716, d3789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2716, d3789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20820 p hg
    simpa only [d2716, d3789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20822 (p : Pattern) (guard : d5850 p = 1) : d2717 p ≤ (0 : Int) + d3790 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2717, d3790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20652 p hg
    simpa only [d2717, d3790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2717, d3790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2717, d3790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20823 (p : Pattern) (guard : d5850 p = 1) : d2718 p ≤ (0 : Int) + d3791 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2718, d3791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20820 p hg
    simpa only [d2718, d3791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2718, d3791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20822 p hg
    simpa only [d2718, d3791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20824 (p : Pattern) (guard : d5850 p = 1) : d2719 p ≤ (0 : Int) + d3792 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2719, d3792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20821 p hg
    simpa only [d2719, d3792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2719, d3792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20823 p hg
    simpa only [d2719, d3792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20825 (p : Pattern) (guard : d5850 p = 1) : d2720 p ≤ (0 : Int) + d3793 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2720, d3793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20787 p hg
    simpa only [d2720, d3793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2720, d3793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20824 p hg
    simpa only [d2720, d3793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20826 (p : Pattern) (guard : d0 p = 1) : d327 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20827 (p : Pattern) (guard : d5850 p = 1) : d2721 p ≤ (0 : Int) + d102 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d5850, d2721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20826 p hg
    simpa only [d5850, d2721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20828 (p : Pattern) (guard : d5850 p = 1) : d2722 p ≤ (0 : Int) + d102 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20827 p hg
    simpa only [d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20751 p hg
    simpa only [d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20829 (p : Pattern) (guard : d5850 p = 1) : d2723 p ≤ (0 : Int) + d3745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2723, d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20828 p hg
    simpa only [d2723, d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2723, d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20757 p hg
    simpa only [d2723, d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20830 (p : Pattern) (guard : d5850 p = 1) : d2724 p ≤ (0 : Int) + d3746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2724, d3746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20829 p hg
    simpa only [d2724, d3746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2724, d3746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20764 p hg
    simpa only [d2724, d3746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20831 (p : Pattern) (guard : d5850 p = 1) : d2702 p ≤ (0 : Int) + d115 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20199 p hg
    simpa only [d5850, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20238 p hg
    simpa only [d5850, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20832 (p : Pattern) (guard : d5850 p = 1) : d2702 p ≤ (0 : Int) + d3794 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2702, d3794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20199 p hg
    simpa only [d5850, d2702, d3794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2702, d3794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20243 p hg
    simpa only [d5850, d2702, d3794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20833 (p : Pattern) (guard : d5850 p = 1) : d2703 p ≤ (0 : Int) + d3769 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20797 p hg
    simpa only [d5850, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20243 p hg
    simpa only [d5850, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20834 (p : Pattern) (guard : d5850 p = 1) : d2704 p ≤ (0 : Int) + d3795 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2704, d3795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20832 p hg
    simpa only [d2704, d3795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2704, d3795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20833 p hg
    simpa only [d2704, d3795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20835 (p : Pattern) (guard : d5850 p = 1) : d2725 p ≤ (0 : Int) + d3796 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2725, d3796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20831 p hg
    simpa only [d2725, d3796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2725, d3796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20834 p hg
    simpa only [d2725, d3796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20836 (p : Pattern) (guard : d5850 p = 1) : d2702 p ≤ (0 : Int) + d3798 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2702, d3798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20199 p hg
    simpa only [d5850, d2702, d3798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2702, d3798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20249 p hg
    simpa only [d5850, d2702, d3798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20837 (p : Pattern) (guard : d5843 p = 1) : d1918 p ≤ (0 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1918, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d5843, d1918, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1918, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20164 p hg
    simpa only [d5843, d1918, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20838 (p : Pattern) (guard : d5843 p = 1) : d1919 p ≤ (0 : Int) + d3797 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1919, d3797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20837 p hg
    simpa only [d1919, d3797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1919, d3797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20166 p hg
    simpa only [d1919, d3797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20839 (p : Pattern) (guard : d5850 p = 1) : d2726 p ≤ (0 : Int) + d3797 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20838 p hg
    simpa only [d5850, d2726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20249 p hg
    simpa only [d5850, d2726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20840 (p : Pattern) (guard : d5850 p = 1) : d2727 p ≤ (0 : Int) + d3799 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2727, d3799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20836 p hg
    simpa only [d2727, d3799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2727, d3799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20839 p hg
    simpa only [d2727, d3799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20841 (p : Pattern) (guard : d5850 p = 1) : d2728 p ≤ (0 : Int) + d3800 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2728, d3800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20840 p hg
    simpa only [d2728, d3800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2728, d3800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2728, d3800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20842 (p : Pattern) (guard : d5850 p = 1) : d2729 p ≤ (0 : Int) + d3801 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2729, d3801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20835 p hg
    simpa only [d2729, d3801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2729, d3801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20841 p hg
    simpa only [d2729, d3801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20843 (p : Pattern) (guard : d5850 p = 1) : d2730 p ≤ (0 : Int) + d3802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2730, d3802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20830 p hg
    simpa only [d2730, d3802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2730, d3802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20842 p hg
    simpa only [d2730, d3802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20844 (p : Pattern) (guard : d5850 p = 1) : d2731 p ≤ (0 : Int) + d3803 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2731, d3803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20782 p hg
    simpa only [d2731, d3803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2731, d3803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20639 p hg
    simpa only [d2731, d3803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20845 (p : Pattern) (guard : d5850 p = 1) : d2732 p ≤ (0 : Int) + d3804 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2732, d3804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20843 p hg
    simpa only [d2732, d3804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2732, d3804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20844 p hg
    simpa only [d2732, d3804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20846 (p : Pattern) (guard : d5850 p = 1) : d2733 p ≤ (0 : Int) + d3805 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2733, d3805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20782 p hg
    simpa only [d2733, d3805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2733, d3805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20643 p hg
    simpa only [d2733, d3805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20847 (p : Pattern) (guard : d5850 p = 1) : d2734 p ≤ (0 : Int) + d3806 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2734, d3806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20846 p hg
    simpa only [d2734, d3806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2734, d3806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2734, d3806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20848 (p : Pattern) (guard : d5850 p = 1) : d2735 p ≤ (0 : Int) + d3807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2735, d3807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20845 p hg
    simpa only [d2735, d3807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2735, d3807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20847 p hg
    simpa only [d2735, d3807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20849 (p : Pattern) (guard : d5850 p = 1) : d2725 p ≤ (0 : Int) + d3808 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2725, d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20831 p hg
    simpa only [d2725, d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2725, d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20800 p hg
    simpa only [d2725, d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20850 (p : Pattern) (guard : d5850 p = 1) : d2736 p ≤ (0 : Int) + d3809 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2736, d3809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20849 p hg
    simpa only [d2736, d3809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2736, d3809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2736, d3809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20851 (p : Pattern) (guard : d5850 p = 1) : d2737 p ≤ (0 : Int) + d3810 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2737, d3810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20810 p hg
    simpa only [d2737, d3810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2737, d3810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20850 p hg
    simpa only [d2737, d3810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20852 (p : Pattern) (guard : d5850 p = 1) : d2738 p ≤ (0 : Int) + d3811 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2738, d3811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20819 p hg
    simpa only [d2738, d3811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2738, d3811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20652 p hg
    simpa only [d2738, d3811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20853 (p : Pattern) (guard : d5850 p = 1) : d2739 p ≤ (0 : Int) + d3812 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2739, d3812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20851 p hg
    simpa only [d2739, d3812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2739, d3812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20852 p hg
    simpa only [d2739, d3812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20854 (p : Pattern) (guard : d5850 p = 1) : d2740 p ≤ (0 : Int) + d3813 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2740, d3813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20819 p hg
    simpa only [d2740, d3813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2740, d3813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20654 p hg
    simpa only [d2740, d3813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20855 (p : Pattern) (guard : d5850 p = 1) : d2741 p ≤ (0 : Int) + d3814 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2741, d3814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20854 p hg
    simpa only [d2741, d3814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2741, d3814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2741, d3814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20856 (p : Pattern) (guard : d5850 p = 1) : d2742 p ≤ (0 : Int) + d3815 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2742, d3815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20853 p hg
    simpa only [d2742, d3815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2742, d3815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20855 p hg
    simpa only [d2742, d3815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20857 (p : Pattern) (guard : d5850 p = 1) : d2743 p ≤ (0 : Int) + d3816 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2743, d3816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20848 p hg
    simpa only [d2743, d3816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2743, d3816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20856 p hg
    simpa only [d2743, d3816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20858 (p : Pattern) (guard : d5850 p = 1) : d2744 p ≤ (0 : Int) + d3817 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2744, d3817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20825 p hg
    simpa only [d2744, d3817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2744, d3817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20857 p hg
    simpa only [d2744, d3817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20859 (p : Pattern) (guard : d5850 p = 1) : d2679 p ≤ (0 : Int) + d3818 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2679, d3818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20755 p hg
    simpa only [d5850, d2679, d3818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2679, d3818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20788 p hg
    simpa only [d5850, d2679, d3818, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
