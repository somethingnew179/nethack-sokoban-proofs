import NetHack.Soko22Hazard87.Compare010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2750 (p : Pattern) (guard : d618 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d617 p = 1 := by simpa only [d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2749 p hg
    simpa only [d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2751 (p : Pattern) (guard : d619 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d618 p = 1 := by simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2750 p hg
    simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2752 (p : Pattern) (guard : d620 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d559 p = 1 := by simpa only [d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2728 p hg
    simpa only [d620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2753 (p : Pattern) (guard : d500 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d486 p = 1 := by simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2730 p hg
    simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2754 (p : Pattern) (guard : d621 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d620 p = 1 := by simpa only [d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2752 p hg
    simpa only [d621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d500 p = 1 := by simpa only [d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2753 p hg
    simpa only [d621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2755 (p : Pattern) (guard : d4413 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d621 p = 1 := by simpa only [d4413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2754 p hg
    simpa only [d4413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d4413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2756 (p : Pattern) (guard : d626 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d500 p = 1 := by simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2753 p hg
    simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2757 (p : Pattern) (guard : d627 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d626 p = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2756 p hg
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2758 (p : Pattern) (guard : d4414 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4413 p = 1 := by simpa only [d4414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2755 p hg
    simpa only [d4414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d627 p = 1 := by simpa only [d4414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2757 p hg
    simpa only [d4414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2759 (p : Pattern) (guard : d51686 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d619 p = 1 := by simpa only [d51686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2751 p hg
    simpa only [d51686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4414 p = 1 := by simpa only [d51686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2758 p hg
    simpa only [d51686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2760 (p : Pattern) (guard : d51687 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d614 p = 1 := by simpa only [d51687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2746 p hg
    simpa only [d51687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51686 p = 1 := by simpa only [d51687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2759 p hg
    simpa only [d51687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2761 (p : Pattern) (guard : d51688 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51684 p = 1 := by simpa only [d51688, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2740 p hg
    simpa only [d51688, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51687 p = 1 := by simpa only [d51688, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2760 p hg
    simpa only [d51688, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2762 (p : Pattern) (guard : d51689 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d51685 p = 1 := by simpa only [d51689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2739 p hg
    simpa only [d51689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51688 p = 1 := by simpa only [d51689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2761 p hg
    simpa only [d51689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2763 (p : Pattern) (guard : d490 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2696 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2764 (p : Pattern) (guard : d491 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d490 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2763 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2765 (p : Pattern) (guard : d633 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d491 p = 1 := by simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2764 p hg
    simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2766 (p : Pattern) (guard : d634 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d633 p = 1 := by simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2765 p hg
    simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2767 (p : Pattern) (guard : d635 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d634 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2766 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2768 (p : Pattern) (guard : d636 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d635 p = 1 := by simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2767 p hg
    simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2769 (p : Pattern) (guard : d637 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d636 p = 1 := by simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2768 p hg
    simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2770 (p : Pattern) (guard : d638 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d496 p = 1 := by simpa only [d638, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d638, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d637 p = 1 := by simpa only [d638, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2769 p hg
    simpa only [d638, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2771 (p : Pattern) (guard : d637 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2772 (p : Pattern) (guard : d501 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d490 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2763 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2773 (p : Pattern) (guard : d639 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d501 p = 1 := by simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2772 p hg
    simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2774 (p : Pattern) (guard : d640 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d639 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2773 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2775 (p : Pattern) (guard : d641 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d640 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2774 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2776 (p : Pattern) (guard : d642 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d641 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2775 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2777 (p : Pattern) (guard : d643 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d642 p = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2776 p hg
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2778 (p : Pattern) (guard : d644 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d637 p = 1 := by simpa only [d644, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2771 p hg
    simpa only [d644, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d643 p = 1 := by simpa only [d644, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2777 p hg
    simpa only [d644, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2779 (p : Pattern) (guard : d645 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d638 p = 1 := by simpa only [d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2770 p hg
    simpa only [d645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d644 p = 1 := by simpa only [d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2778 p hg
    simpa only [d645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2780 (p : Pattern) (guard : d51690 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d51689 p = 1 := by simpa only [d51690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2762 p hg
    simpa only [d51690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d645 p = 1 := by simpa only [d51690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2779 p hg
    simpa only [d51690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2781 (p : Pattern) (guard : d51691 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d51690 p = 1 := by simpa only [d51691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2780 p hg
    simpa only [d51691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d51691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2782 (p : Pattern) (guard : d64433 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d64433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51691 p = 1 := by simpa only [d64433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2781 p hg
    simpa only [d64433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2783 (p : Pattern) (guard : d64434 p = 1) : d47768 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d64433 p = 1 := by simpa only [d64434, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2782 p hg
    simpa only [d64434, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64434, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d64434, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2784 (p : Pattern) (guard : d64435 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d64434 p = 1 := by simpa only [d64435, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2783 p hg
    simpa only [d64435, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64435, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d64435, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2785 (p : Pattern) (guard : d64436 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64435 p = 1 := by simpa only [d64436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2784 p hg
    simpa only [d64436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2786 (p : Pattern) (guard : d64437 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64436 p = 1 := by simpa only [d64437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2785 p hg
    simpa only [d64437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2787 (p : Pattern) (guard : d64438 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64437 p = 1 := by simpa only [d64438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2786 p hg
    simpa only [d64438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2788 (p : Pattern) (guard : d64439 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64438 p = 1 := by simpa only [d64439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2787 p hg
    simpa only [d64439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2789 (p : Pattern) (guard : d64440 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64439 p = 1 := by simpa only [d64440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2788 p hg
    simpa only [d64440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2790 (p : Pattern) (guard : d64441 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64440 p = 1 := by simpa only [d64441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2789 p hg
    simpa only [d64441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2791 (p : Pattern) (guard : d64442 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d64432 p = 1 := by simpa only [d64442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2681 p hg
    simpa only [d64442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64441 p = 1 := by simpa only [d64442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2790 p hg
    simpa only [d64442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2792 (p : Pattern) (guard : d751 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare363 p hg
    simpa only [d751, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d751, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2793 (p : Pattern) (guard : d752 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d751 p = 1 := by simpa only [d752, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2792 p hg
    simpa only [d752, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d752, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d752, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2794 (p : Pattern) (guard : d753 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d753, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2793 p hg
    simpa only [d753, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2795 (p : Pattern) (guard : d754 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2794 p hg
    simpa only [d754, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d754, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2796 (p : Pattern) (guard : d755 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2617 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2795 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2797 (p : Pattern) (guard : d756 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d547 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2716 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d755 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2796 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2798 (p : Pattern) (guard : d757 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2795 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2799 (p : Pattern) (guard : d758 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2796 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2798 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2800 (p : Pattern) (guard : d759 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d756 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2797 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2799 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2801 (p : Pattern) (guard : d760 p = 1) : d47686 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d760, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d760, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d759 p = 1 := by simpa only [d760, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2800 p hg
    simpa only [d760, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2802 (p : Pattern) (guard : d761 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d761, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d761, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d760 p = 1 := by simpa only [d761, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2801 p hg
    simpa only [d761, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2803 (p : Pattern) (guard : d762 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2798 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2804 (p : Pattern) (guard : d763 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2799 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2803 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2805 (p : Pattern) (guard : d764 p = 1) : d47686 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d764, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d764, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d763 p = 1 := by simpa only [d764, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2804 p hg
    simpa only [d764, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2806 (p : Pattern) (guard : d765 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d765, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2805 p hg
    simpa only [d765, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2807 (p : Pattern) (guard : d766 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d761 p = 1 := by simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2802 p hg
    simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2806 p hg
    simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2808 (p : Pattern) (guard : d767 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2806 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2809 (p : Pattern) (guard : d768 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d766 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2807 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2808 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2810 (p : Pattern) (guard : d769 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2809 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2811 (p : Pattern) (guard : d770 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d770, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2810 p hg
    simpa only [d770, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d770, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2812 (p : Pattern) (guard : d771 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d771, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d771, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d771, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2811 p hg
    simpa only [d771, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2813 (p : Pattern) (guard : d772 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2808 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2814 (p : Pattern) (guard : d773 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2813 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2815 (p : Pattern) (guard : d774 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2814 p hg
    simpa only [d774, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d774, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2816 (p : Pattern) (guard : d775 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d775, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2815 p hg
    simpa only [d775, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2817 (p : Pattern) (guard : d776 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d771 p = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2812 p hg
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2816 p hg
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2818 (p : Pattern) (guard : d777 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d776 p = 1 := by simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2817 p hg
    simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2819 (p : Pattern) (guard : d803 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d777 p = 1 := by simpa only [d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2818 p hg
    simpa only [d803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2820 (p : Pattern) (guard : d804 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d803 p = 1 := by simpa only [d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2821 (p : Pattern) (guard : d780 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2816 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2822 (p : Pattern) (guard : d781 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2821 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2823 (p : Pattern) (guard : d805 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d781 p = 1 := by simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2822 p hg
    simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2824 (p : Pattern) (guard : d806 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d805 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2823 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2825 (p : Pattern) (guard : d807 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d804 p = 1 := by simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2820 p hg
    simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d806 p = 1 := by simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2824 p hg
    simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2826 (p : Pattern) (guard : d808 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d807 p = 1 := by simpa only [d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2825 p hg
    simpa only [d808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2827 (p : Pattern) (guard : d809 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d808 p = 1 := by simpa only [d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2826 p hg
    simpa only [d809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2828 (p : Pattern) (guard : d810 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d809 p = 1 := by simpa only [d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2827 p hg
    simpa only [d810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2829 (p : Pattern) (guard : d811 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d776 p = 1 := by simpa only [d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2817 p hg
    simpa only [d811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2830 (p : Pattern) (guard : d812 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d811 p = 1 := by simpa only [d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2829 p hg
    simpa only [d812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2831 (p : Pattern) (guard : d813 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d812 p = 1 := by simpa only [d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2830 p hg
    simpa only [d813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2832 (p : Pattern) (guard : d814 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d780 p = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2821 p hg
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2833 (p : Pattern) (guard : d815 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d814 p = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2832 p hg
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2834 (p : Pattern) (guard : d816 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d815 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2833 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2835 (p : Pattern) (guard : d817 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d813 p = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2831 p hg
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d816 p = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2834 p hg
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2836 (p : Pattern) (guard : d818 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d817 p = 1 := by simpa only [d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2835 p hg
    simpa only [d818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2837 (p : Pattern) (guard : d819 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2836 p hg
    simpa only [d819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2838 (p : Pattern) (guard : d834 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d833 p = 1 := by simpa only [d834, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare354 p hg
    simpa only [d834, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d834, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d834, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2839 (p : Pattern) (guard : d835 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d834 p = 1 := by simpa only [d835, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2838 p hg
    simpa only [d835, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d835, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2840 (p : Pattern) (guard : d836 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d836, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d836, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d836, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2839 p hg
    simpa only [d836, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2841 (p : Pattern) (guard : d837 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d836 p = 1 := by simpa only [d837, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2840 p hg
    simpa only [d837, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d837, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d837, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2842 (p : Pattern) (guard : d838 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d837 p = 1 := by simpa only [d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2841 p hg
    simpa only [d838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d546 p = 1 := by simpa only [d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2715 p hg
    simpa only [d838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2843 (p : Pattern) (guard : d839 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d838 p = 1 := by simpa only [d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2842 p hg
    simpa only [d839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d547 p = 1 := by simpa only [d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2716 p hg
    simpa only [d839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2844 (p : Pattern) (guard : d840 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d839 p = 1 := by simpa only [d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2843 p hg
    simpa only [d840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d756 p = 1 := by simpa only [d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2797 p hg
    simpa only [d840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2845 (p : Pattern) (guard : d841 p = 1) : d47686 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d841, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d841, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d840 p = 1 := by simpa only [d841, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2844 p hg
    simpa only [d841, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2846 (p : Pattern) (guard : d842 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d842, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d842, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d842, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2845 p hg
    simpa only [d842, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2847 (p : Pattern) (guard : d843 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d842 p = 1 := by simpa only [d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2846 p hg
    simpa only [d843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d761 p = 1 := by simpa only [d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2802 p hg
    simpa only [d843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2848 (p : Pattern) (guard : d844 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d843 p = 1 := by simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2847 p hg
    simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d766 p = 1 := by simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2807 p hg
    simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2849 (p : Pattern) (guard : d845 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d844 p = 1 := by simpa only [d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2848 p hg
    simpa only [d845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2850 (p : Pattern) (guard : d846 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d845 p = 1 := by simpa only [d846, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2849 p hg
    simpa only [d846, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d846, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d846, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2851 (p : Pattern) (guard : d847 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d847, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d847, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d846 p = 1 := by simpa only [d847, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2850 p hg
    simpa only [d847, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2852 (p : Pattern) (guard : d848 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d847 p = 1 := by simpa only [d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2851 p hg
    simpa only [d848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d771 p = 1 := by simpa only [d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2812 p hg
    simpa only [d848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2853 (p : Pattern) (guard : d849 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d848 p = 1 := by simpa only [d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2852 p hg
    simpa only [d849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2854 (p : Pattern) (guard : d850 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d849 p = 1 := by simpa only [d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2853 p hg
    simpa only [d850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2855 (p : Pattern) (guard : d851 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2854 p hg
    simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2856 (p : Pattern) (guard : d778 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d777 p = 1 := by simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2818 p hg
    simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2857 (p : Pattern) (guard : d779 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d778 p = 1 := by simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2856 p hg
    simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2858 (p : Pattern) (guard : d852 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2855 p hg
    simpa only [d852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d779 p = 1 := by simpa only [d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2857 p hg
    simpa only [d852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2859 (p : Pattern) (guard : d4446 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d852 p = 1 := by simpa only [d4446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2858 p hg
    simpa only [d4446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d4446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2860 (p : Pattern) (guard : d909 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d779 p = 1 := by simpa only [d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2857 p hg
    simpa only [d909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2861 (p : Pattern) (guard : d910 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d909 p = 1 := by simpa only [d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2860 p hg
    simpa only [d910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2862 (p : Pattern) (guard : d4447 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4446 p = 1 := by simpa only [d4447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2859 p hg
    simpa only [d4447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d4447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2861 p hg
    simpa only [d4447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2863 (p : Pattern) (guard : d51709 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d819 p = 1 := by simpa only [d51709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2837 p hg
    simpa only [d51709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4447 p = 1 := by simpa only [d51709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2862 p hg
    simpa only [d51709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2864 (p : Pattern) (guard : d51710 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d810 p = 1 := by simpa only [d51710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2828 p hg
    simpa only [d51710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51709 p = 1 := by simpa only [d51710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2863 p hg
    simpa only [d51710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2865 (p : Pattern) (guard : d51711 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51711, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d51711, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51710 p = 1 := by simpa only [d51711, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2864 p hg
    simpa only [d51711, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2866 (p : Pattern) (guard : d51710 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2867 (p : Pattern) (guard : d915 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d803 p = 1 := by simpa only [d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2868 (p : Pattern) (guard : d916 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d805 p = 1 := by simpa only [d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2823 p hg
    simpa only [d916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2869 (p : Pattern) (guard : d917 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2867 p hg
    simpa only [d917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2868 p hg
    simpa only [d917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2870 (p : Pattern) (guard : d918 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2869 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2871 (p : Pattern) (guard : d919 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2870 p hg
    simpa only [d919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2872 (p : Pattern) (guard : d920 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d919 p = 1 := by simpa only [d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2871 p hg
    simpa only [d920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2873 (p : Pattern) (guard : d921 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d812 p = 1 := by simpa only [d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2830 p hg
    simpa only [d921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2874 (p : Pattern) (guard : d922 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d815 p = 1 := by simpa only [d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2833 p hg
    simpa only [d922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2875 (p : Pattern) (guard : d923 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d921 p = 1 := by simpa only [d923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2873 p hg
    simpa only [d923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d922 p = 1 := by simpa only [d923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2874 p hg
    simpa only [d923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2876 (p : Pattern) (guard : d924 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d923 p = 1 := by simpa only [d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2875 p hg
    simpa only [d924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2877 (p : Pattern) (guard : d925 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d924 p = 1 := by simpa only [d925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2876 p hg
    simpa only [d925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2878 (p : Pattern) (guard : d926 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2854 p hg
    simpa only [d926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2879 (p : Pattern) (guard : d792 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d778 p = 1 := by simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2856 p hg
    simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2880 (p : Pattern) (guard : d927 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d926 p = 1 := by simpa only [d927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2878 p hg
    simpa only [d927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d792 p = 1 := by simpa only [d927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2879 p hg
    simpa only [d927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2881 (p : Pattern) (guard : d4451 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d927 p = 1 := by simpa only [d4451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2880 p hg
    simpa only [d4451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d4451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2882 (p : Pattern) (guard : d932 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d792 p = 1 := by simpa only [d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2879 p hg
    simpa only [d932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2883 (p : Pattern) (guard : d933 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d932 p = 1 := by simpa only [d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2882 p hg
    simpa only [d933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2884 (p : Pattern) (guard : d4452 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4451 p = 1 := by simpa only [d4452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2881 p hg
    simpa only [d4452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d933 p = 1 := by simpa only [d4452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2883 p hg
    simpa only [d4452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2885 (p : Pattern) (guard : d51712 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d925 p = 1 := by simpa only [d51712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2877 p hg
    simpa only [d51712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4452 p = 1 := by simpa only [d51712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2884 p hg
    simpa only [d51712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2886 (p : Pattern) (guard : d51713 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d920 p = 1 := by simpa only [d51713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2872 p hg
    simpa only [d51713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51712 p = 1 := by simpa only [d51713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2885 p hg
    simpa only [d51713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2887 (p : Pattern) (guard : d51714 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51710 p = 1 := by simpa only [d51714, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2866 p hg
    simpa only [d51714, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51713 p = 1 := by simpa only [d51714, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2886 p hg
    simpa only [d51714, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2888 (p : Pattern) (guard : d51715 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d51711 p = 1 := by simpa only [d51715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2865 p hg
    simpa only [d51715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51714 p = 1 := by simpa only [d51715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2887 p hg
    simpa only [d51715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2889 (p : Pattern) (guard : d782 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2822 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2890 (p : Pattern) (guard : d783 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d782 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2889 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2891 (p : Pattern) (guard : d939 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d783 p = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2890 p hg
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2892 (p : Pattern) (guard : d940 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d939 p = 1 := by simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2891 p hg
    simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2893 (p : Pattern) (guard : d941 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d940 p = 1 := by simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2892 p hg
    simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2894 (p : Pattern) (guard : d942 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d941 p = 1 := by simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2893 p hg
    simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2895 (p : Pattern) (guard : d943 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d942 p = 1 := by simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2894 p hg
    simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2896 (p : Pattern) (guard : d944 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d788 p = 1 := by simpa only [d944, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2363 p hg
    simpa only [d944, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d943 p = 1 := by simpa only [d944, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2895 p hg
    simpa only [d944, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2897 (p : Pattern) (guard : d943 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2898 (p : Pattern) (guard : d793 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d782 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2889 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2899 (p : Pattern) (guard : d945 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2898 p hg
    simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2900 (p : Pattern) (guard : d946 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d945 p = 1 := by simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2899 p hg
    simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2901 (p : Pattern) (guard : d947 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d946 p = 1 := by simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2900 p hg
    simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2902 (p : Pattern) (guard : d948 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d947 p = 1 := by simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2901 p hg
    simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2903 (p : Pattern) (guard : d949 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d948 p = 1 := by simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2902 p hg
    simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2904 (p : Pattern) (guard : d950 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d943 p = 1 := by simpa only [d950, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d950, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d949 p = 1 := by simpa only [d950, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2903 p hg
    simpa only [d950, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2905 (p : Pattern) (guard : d951 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d944 p = 1 := by simpa only [d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2896 p hg
    simpa only [d951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d950 p = 1 := by simpa only [d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2904 p hg
    simpa only [d951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2906 (p : Pattern) (guard : d51716 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d51715 p = 1 := by simpa only [d51716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2888 p hg
    simpa only [d51716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d951 p = 1 := by simpa only [d51716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2905 p hg
    simpa only [d51716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2907 (p : Pattern) (guard : d51717 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d51716 p = 1 := by simpa only [d51717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2906 p hg
    simpa only [d51717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d51717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2908 (p : Pattern) (guard : d64443 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d64443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51717 p = 1 := by simpa only [d64443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2907 p hg
    simpa only [d64443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2909 (p : Pattern) (guard : d64444 p = 1) : d47768 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d64443 p = 1 := by simpa only [d64444, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2908 p hg
    simpa only [d64444, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64444, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d64444, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2910 (p : Pattern) (guard : d64445 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d64444 p = 1 := by simpa only [d64445, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2909 p hg
    simpa only [d64445, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64445, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d64445, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2911 (p : Pattern) (guard : d64446 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64445 p = 1 := by simpa only [d64446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2910 p hg
    simpa only [d64446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2912 (p : Pattern) (guard : d64447 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64446 p = 1 := by simpa only [d64447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2911 p hg
    simpa only [d64447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2913 (p : Pattern) (guard : d64448 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64447 p = 1 := by simpa only [d64448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2912 p hg
    simpa only [d64448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2914 (p : Pattern) (guard : d64449 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64448 p = 1 := by simpa only [d64449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2913 p hg
    simpa only [d64449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2915 (p : Pattern) (guard : d64450 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64449 p = 1 := by simpa only [d64450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2914 p hg
    simpa only [d64450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2916 (p : Pattern) (guard : d64451 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64450 p = 1 := by simpa only [d64451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2915 p hg
    simpa only [d64451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2917 (p : Pattern) (guard : d64452 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64451 p = 1 := by simpa only [d64452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2916 p hg
    simpa only [d64452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2918 (p : Pattern) (guard : d64453 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d64442 p = 1 := by simpa only [d64453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2791 p hg
    simpa only [d64453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64452 p = 1 := by simpa only [d64453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2917 p hg
    simpa only [d64453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2919 (p : Pattern) (guard : d1100 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare499 p hg
    simpa only [d1100, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d1100, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2920 (p : Pattern) (guard : d1101 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1100 p = 1 := by simpa only [d1101, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2919 p hg
    simpa only [d1101, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1101, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d1101, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2921 (p : Pattern) (guard : d1102 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1102, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d1102, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1102, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2920 p hg
    simpa only [d1102, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2922 (p : Pattern) (guard : d1103 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2921 p hg
    simpa only [d1103, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d1103, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2923 (p : Pattern) (guard : d1110 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare517 p hg
    simpa only [d1110, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d1110, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2924 (p : Pattern) (guard : d1111 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1110 p = 1 := by simpa only [d1111, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2923 p hg
    simpa only [d1111, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1111, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d1111, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2925 (p : Pattern) (guard : d1112 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d1112, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2924 p hg
    simpa only [d1112, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2926 (p : Pattern) (guard : d1113 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2925 p hg
    simpa only [d1113, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d1113, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2927 (p : Pattern) (guard : d1114 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2922 p hg
    simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1113 p = 1 := by simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2926 p hg
    simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2928 (p : Pattern) (guard : d1121 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d1121, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d1121, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2929 (p : Pattern) (guard : d1122 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1121 p = 1 := by simpa only [d1122, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2928 p hg
    simpa only [d1122, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d1122, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2930 (p : Pattern) (guard : d1123 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d1123, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2929 p hg
    simpa only [d1123, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2931 (p : Pattern) (guard : d1124 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2930 p hg
    simpa only [d1124, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d1124, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2932 (p : Pattern) (guard : d1125 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2926 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2931 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2933 (p : Pattern) (guard : d1126 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1114 p = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2932 p hg
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2934 (p : Pattern) (guard : d1127 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2931 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2935 (p : Pattern) (guard : d1128 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2932 p hg
    simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1127 p = 1 := by simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2934 p hg
    simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2936 (p : Pattern) (guard : d1129 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2933 p hg
    simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1128 p = 1 := by simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2935 p hg
    simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2937 (p : Pattern) (guard : d1130 p = 1) : d47686 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1130, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d1130, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1129 p = 1 := by simpa only [d1130, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2936 p hg
    simpa only [d1130, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2938 (p : Pattern) (guard : d1131 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1131, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d1131, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1130 p = 1 := by simpa only [d1131, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2937 p hg
    simpa only [d1131, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2939 (p : Pattern) (guard : d1136 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1135 p = 1 := by simpa only [d1136, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare560 p hg
    simpa only [d1136, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1136, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d1136, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2940 (p : Pattern) (guard : d1137 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1136 p = 1 := by simpa only [d1137, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2939 p hg
    simpa only [d1137, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1137, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d1137, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2941 (p : Pattern) (guard : d1138 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1138, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d1138, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1137 p = 1 := by simpa only [d1138, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2940 p hg
    simpa only [d1138, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2942 (p : Pattern) (guard : d1139 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1138 p = 1 := by simpa only [d1139, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2941 p hg
    simpa only [d1139, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1139, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d1139, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2943 (p : Pattern) (guard : d1140 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1139 p = 1 := by simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2942 p hg
    simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2944 (p : Pattern) (guard : d1141 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2934 p hg
    simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1140 p = 1 := by simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2943 p hg
    simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2945 (p : Pattern) (guard : d1142 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1128 p = 1 := by simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2935 p hg
    simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1141 p = 1 := by simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2944 p hg
    simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2946 (p : Pattern) (guard : d1143 p = 1) : d47686 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1143, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d1143, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1142 p = 1 := by simpa only [d1143, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2945 p hg
    simpa only [d1143, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2947 (p : Pattern) (guard : d1144 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1144, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d1144, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1143 p = 1 := by simpa only [d1144, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2946 p hg
    simpa only [d1144, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2948 (p : Pattern) (guard : d1145 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1131 p = 1 := by simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2938 p hg
    simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1144 p = 1 := by simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2947 p hg
    simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2949 (p : Pattern) (guard : d1146 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1144 p = 1 := by simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2947 p hg
    simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2950 (p : Pattern) (guard : d1147 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1145 p = 1 := by simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2948 p hg
    simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1146 p = 1 := by simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2949 p hg
    simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2951 (p : Pattern) (guard : d1148 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1147 p = 1 := by simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2950 p hg
    simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2952 (p : Pattern) (guard : d1149 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d1149, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2951 p hg
    simpa only [d1149, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1149, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d1149, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2953 (p : Pattern) (guard : d1150 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d1150, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1149 p = 1 := by simpa only [d1150, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2952 p hg
    simpa only [d1150, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2954 (p : Pattern) (guard : d1151 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1146 p = 1 := by simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2949 p hg
    simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2955 (p : Pattern) (guard : d1152 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2954 p hg
    simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2956 (p : Pattern) (guard : d1153 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1152 p = 1 := by simpa only [d1153, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2955 p hg
    simpa only [d1153, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1153, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d1153, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2957 (p : Pattern) (guard : d1154 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1154, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d1154, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1153 p = 1 := by simpa only [d1154, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2956 p hg
    simpa only [d1154, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2958 (p : Pattern) (guard : d1155 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2953 p hg
    simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1154 p = 1 := by simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2957 p hg
    simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2959 (p : Pattern) (guard : d1156 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1155 p = 1 := by simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2958 p hg
    simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2960 (p : Pattern) (guard : d1182 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1156 p = 1 := by simpa only [d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2959 p hg
    simpa only [d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2961 (p : Pattern) (guard : d1183 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1182 p = 1 := by simpa only [d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2960 p hg
    simpa only [d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2962 (p : Pattern) (guard : d1159 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1154 p = 1 := by simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2957 p hg
    simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2963 (p : Pattern) (guard : d1160 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1159 p = 1 := by simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2962 p hg
    simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2964 (p : Pattern) (guard : d1184 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1160 p = 1 := by simpa only [d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2963 p hg
    simpa only [d1184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2965 (p : Pattern) (guard : d1185 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1184 p = 1 := by simpa only [d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2964 p hg
    simpa only [d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2966 (p : Pattern) (guard : d1186 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1183 p = 1 := by simpa only [d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2961 p hg
    simpa only [d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1185 p = 1 := by simpa only [d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2965 p hg
    simpa only [d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2967 (p : Pattern) (guard : d1187 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1186 p = 1 := by simpa only [d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2966 p hg
    simpa only [d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2968 (p : Pattern) (guard : d1188 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1187 p = 1 := by simpa only [d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2967 p hg
    simpa only [d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2969 (p : Pattern) (guard : d1189 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1188 p = 1 := by simpa only [d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2968 p hg
    simpa only [d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2970 (p : Pattern) (guard : d1190 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1155 p = 1 := by simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2958 p hg
    simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2971 (p : Pattern) (guard : d1191 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1190 p = 1 := by simpa only [d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2970 p hg
    simpa only [d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2972 (p : Pattern) (guard : d1192 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1191 p = 1 := by simpa only [d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2971 p hg
    simpa only [d1192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2973 (p : Pattern) (guard : d1193 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1159 p = 1 := by simpa only [d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2962 p hg
    simpa only [d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2974 (p : Pattern) (guard : d1194 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1193 p = 1 := by simpa only [d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2973 p hg
    simpa only [d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2975 (p : Pattern) (guard : d1195 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1194 p = 1 := by simpa only [d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2974 p hg
    simpa only [d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2976 (p : Pattern) (guard : d1196 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1192 p = 1 := by simpa only [d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2972 p hg
    simpa only [d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1195 p = 1 := by simpa only [d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2975 p hg
    simpa only [d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2977 (p : Pattern) (guard : d1197 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1196 p = 1 := by simpa only [d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2976 p hg
    simpa only [d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2978 (p : Pattern) (guard : d1198 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1197 p = 1 := by simpa only [d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2977 p hg
    simpa only [d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2979 (p : Pattern) (guard : d1210 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1209 p = 1 := by simpa only [d1210, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare480 p hg
    simpa only [d1210, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1210, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d1210, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2980 (p : Pattern) (guard : d1211 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1210 p = 1 := by simpa only [d1211, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2979 p hg
    simpa only [d1211, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1211, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d1211, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2981 (p : Pattern) (guard : d1212 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1212, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d1212, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1211 p = 1 := by simpa only [d1212, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2980 p hg
    simpa only [d1212, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2982 (p : Pattern) (guard : d1213 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1212 p = 1 := by simpa only [d1213, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2981 p hg
    simpa only [d1213, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1213, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d1213, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2983 (p : Pattern) (guard : d1214 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1213 p = 1 := by simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2982 p hg
    simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1103 p = 1 := by simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2922 p hg
    simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2984 (p : Pattern) (guard : d1215 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1214 p = 1 := by simpa only [d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2983 p hg
    simpa only [d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1114 p = 1 := by simpa only [d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2985 (p : Pattern) (guard : d1216 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1215 p = 1 := by simpa only [d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2984 p hg
    simpa only [d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2933 p hg
    simpa only [d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2986 (p : Pattern) (guard : d1217 p = 1) : d47686 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1217, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d1217, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1216 p = 1 := by simpa only [d1217, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2985 p hg
    simpa only [d1217, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2987 (p : Pattern) (guard : d1218 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1218, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d1218, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1217 p = 1 := by simpa only [d1218, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2986 p hg
    simpa only [d1218, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2988 (p : Pattern) (guard : d1219 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1218 p = 1 := by simpa only [d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2987 p hg
    simpa only [d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1131 p = 1 := by simpa only [d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2938 p hg
    simpa only [d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2989 (p : Pattern) (guard : d1220 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1219 p = 1 := by simpa only [d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2988 p hg
    simpa only [d1220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1145 p = 1 := by simpa only [d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2948 p hg
    simpa only [d1220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2990 (p : Pattern) (guard : d1221 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1220 p = 1 := by simpa only [d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2989 p hg
    simpa only [d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2991 (p : Pattern) (guard : d1222 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1221 p = 1 := by simpa only [d1222, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2990 p hg
    simpa only [d1222, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1222, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d1222, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2992 (p : Pattern) (guard : d1223 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1223, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d1223, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1222 p = 1 := by simpa only [d1223, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2991 p hg
    simpa only [d1223, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2993 (p : Pattern) (guard : d1224 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1223 p = 1 := by simpa only [d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2992 p hg
    simpa only [d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1150 p = 1 := by simpa only [d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2953 p hg
    simpa only [d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2994 (p : Pattern) (guard : d1225 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1224 p = 1 := by simpa only [d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2993 p hg
    simpa only [d1225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2995 (p : Pattern) (guard : d1226 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1225 p = 1 := by simpa only [d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2994 p hg
    simpa only [d1226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2996 (p : Pattern) (guard : d1227 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1226 p = 1 := by simpa only [d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2995 p hg
    simpa only [d1227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2997 (p : Pattern) (guard : d1157 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1156 p = 1 := by simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2959 p hg
    simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2998 (p : Pattern) (guard : d1158 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1157 p = 1 := by simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2997 p hg
    simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2999 (p : Pattern) (guard : d1228 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1227 p = 1 := by simpa only [d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2996 p hg
    simpa only [d1228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2998 p hg
    simpa only [d1228, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
