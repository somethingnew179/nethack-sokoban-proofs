/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2660 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d312 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2661 (p : Pattern) (guard : d912 p = 1) : d275 p ≤ (0 : Int) + d312 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare833 p hg
    simpa only [d912, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2660 p hg
    simpa only [d912, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2662 (p : Pattern) (guard : d912 p = 1) : d276 p ≤ (0 : Int) + d313 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d276, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2654 p hg
    simpa only [d276, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d276, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2661 p hg
    simpa only [d276, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2663 (p : Pattern) (guard : d912 p = 1) : d277 p ≤ (0 : Int) + d314 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d277, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2659 p hg
    simpa only [d277, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d277, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2662 p hg
    simpa only [d277, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2664 (p : Pattern) (guard : d912 p = 1) : d278 p ≤ (0 : Int) + d315 p := by
  cases selected : p 106 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d278, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2656 p hg
    simpa only [d278, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d278, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2663 p hg
    simpa only [d278, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2665 (p : Pattern) (guard : d912 p = 1) : d279 p ≤ (0 : Int) + d316 p := by
  cases selected : p 86 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d279, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2647 p hg
    simpa only [d279, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d279, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2664 p hg
    simpa only [d279, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2666 (p : Pattern) (guard : d910 p = 1) : d28 p ≤ (0 : Int) + d298 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d28, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d910, d28, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d28, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1189 p hg
    simpa only [d910, d28, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2667 (p : Pattern) (guard : d0 p = 1) : d160 p ≤ (0 : Int) + d317 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2668 (p : Pattern) (guard : d912 p = 1) : d280 p ≤ (0 : Int) + d318 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d280, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2666 p hg
    simpa only [d912, d280, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d280, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2667 p hg
    simpa only [d912, d280, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2669 (p : Pattern) (guard : d912 p = 1) : d281 p ≤ (0 : Int) + d319 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d281, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2641 p hg
    simpa only [d281, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d281, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2668 p hg
    simpa only [d281, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2670 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d294 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2671 (p : Pattern) (guard : d912 p = 1) : d282 p ≤ (0 : Int) + d294 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare793 p hg
    simpa only [d912, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2670 p hg
    simpa only [d912, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2672 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d295 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2673 (p : Pattern) (guard : d912 p = 1) : d283 p ≤ (0 : Int) + d295 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare798 p hg
    simpa only [d912, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2672 p hg
    simpa only [d912, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2674 (p : Pattern) (guard : d912 p = 1) : d284 p ≤ (0 : Int) + d296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d284, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2671 p hg
    simpa only [d284, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d284, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2673 p hg
    simpa only [d284, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2675 (p : Pattern) (guard : d912 p = 1) : d285 p ≤ (0 : Int) + d320 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d285, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2669 p hg
    simpa only [d285, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d285, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2674 p hg
    simpa only [d285, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2676 (p : Pattern) (guard : d912 p = 1) : d286 p ≤ (0 : Int) + d321 p := by
  cases selected : p 106 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d286, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2646 p hg
    simpa only [d286, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d286, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2675 p hg
    simpa only [d286, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2677 (p : Pattern) (guard : d912 p = 1) : d287 p ≤ (0 : Int) + d322 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d287, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2668 p hg
    simpa only [d287, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d287, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2673 p hg
    simpa only [d287, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2678 (p : Pattern) (guard : d912 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare2679 (p : Pattern) (guard : d912 p = 1) : d288 p ≤ (0 : Int) + d323 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d288, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2661 p hg
    simpa only [d288, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d288, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2678 p hg
    simpa only [d288, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2680 (p : Pattern) (guard : d912 p = 1) : d289 p ≤ (0 : Int) + d324 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d289, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2677 p hg
    simpa only [d289, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d289, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2679 p hg
    simpa only [d289, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2681 (p : Pattern) (guard : d912 p = 1) : d290 p ≤ (0 : Int) + d325 p := by
  cases selected : p 106 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d290, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2663 p hg
    simpa only [d290, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d290, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2680 p hg
    simpa only [d290, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2682 (p : Pattern) (guard : d912 p = 1) : d291 p ≤ (0 : Int) + d326 p := by
  cases selected : p 86 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d291, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2676 p hg
    simpa only [d291, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d291, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2681 p hg
    simpa only [d291, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2683 (p : Pattern) (guard : d912 p = 1) : d292 p ≤ (0 : Int) + d327 p := by
  cases selected : p 80 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d292, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2665 p hg
    simpa only [d292, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d292, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2682 p hg
    simpa only [d292, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2684 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2685 (p : Pattern) (guard : d1150 p = 1) : d28 p ≤ (0 : Int) + d16 p := by
  cases selected : p 133 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2684 p hg
    simpa only [d1150, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d1150, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d1150, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2686 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2687 (p : Pattern) (guard : d1151 p = 1) : d256 p ≤ (0 : Int) + d16 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2685 p hg
    simpa only [d1151, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2686 p hg
    simpa only [d1151, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2688 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2689 (p : Pattern) (guard : d1150 p = 1) : d47 p ≤ (0 : Int) + d15 p := by
  cases selected : p 133 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2688 p hg
    simpa only [d1150, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d1150, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1139 p hg
    simpa only [d1150, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2690 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2691 (p : Pattern) (guard : d1151 p = 1) : d257 p ≤ (0 : Int) + d15 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2689 p hg
    simpa only [d1151, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2690 p hg
    simpa only [d1151, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2692 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2693 (p : Pattern) (guard : d1150 p = 1) : d57 p ≤ (0 : Int) + d53 p := by
  cases selected : p 133 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2692 p hg
    simpa only [d1150, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d1150, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1144 p hg
    simpa only [d1150, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2694 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2695 (p : Pattern) (guard : d1151 p = 1) : d258 p ≤ (0 : Int) + d53 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2693 p hg
    simpa only [d1151, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2694 p hg
    simpa only [d1151, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2696 (p : Pattern) (guard : d1151 p = 1) : d259 p ≤ (0 : Int) + d1152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d259, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2691 p hg
    simpa only [d259, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d259, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2695 p hg
    simpa only [d259, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2697 (p : Pattern) (guard : d1151 p = 1) : d260 p ≤ (0 : Int) + d1153 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d260, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2687 p hg
    simpa only [d260, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d260, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2696 p hg
    simpa only [d260, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2698 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2699 (p : Pattern) (guard : d1151 p = 1) : d261 p ≤ (0 : Int) + d16 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2685 p hg
    simpa only [d1151, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2698 p hg
    simpa only [d1151, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2700 (p : Pattern) (guard : d1151 p = 1) : d262 p ≤ (0 : Int) + d16 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2687 p hg
    simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2699 p hg
    simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2701 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2702 (p : Pattern) (guard : d1151 p = 1) : d263 p ≤ (0 : Int) + d53 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2693 p hg
    simpa only [d1151, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2701 p hg
    simpa only [d1151, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2703 (p : Pattern) (guard : d1151 p = 1) : d264 p ≤ (0 : Int) + d1152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d264, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2691 p hg
    simpa only [d264, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d264, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2702 p hg
    simpa only [d264, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2704 (p : Pattern) (guard : d1151 p = 1) : d265 p ≤ (0 : Int) + d1153 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d265, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2700 p hg
    simpa only [d265, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d265, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2703 p hg
    simpa only [d265, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2705 (p : Pattern) (guard : d1151 p = 1) : d266 p ≤ (0 : Int) + d1153 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2697 p hg
    simpa only [d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2704 p hg
    simpa only [d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2706 (p : Pattern) (guard : d0 p = 1) : d86 p ≤ (0 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2707 (p : Pattern) (guard : d1150 p = 1) : d89 p ≤ (0 : Int) + d86 p := by
  cases selected : p 133 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2706 p hg
    simpa only [d1150, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d1150, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d1150, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2708 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2709 (p : Pattern) (guard : d1151 p = 1) : d267 p ≤ (0 : Int) + d86 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2707 p hg
    simpa only [d1151, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2708 p hg
    simpa only [d1151, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2710 (p : Pattern) (guard : d1151 p = 1) : d268 p ≤ (0 : Int) + d1154 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d268, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2687 p hg
    simpa only [d268, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d268, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2709 p hg
    simpa only [d268, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2711 (p : Pattern) (guard : d0 p = 1) : d98 p ≤ (0 : Int) + d98 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2712 (p : Pattern) (guard : d1150 p = 1) : d100 p ≤ (0 : Int) + d98 p := by
  cases selected : p 133 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2711 p hg
    simpa only [d1150, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d1150, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1161 p hg
    simpa only [d1150, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2713 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d98 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2714 (p : Pattern) (guard : d1151 p = 1) : d269 p ≤ (0 : Int) + d98 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2712 p hg
    simpa only [d1151, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2713 p hg
    simpa only [d1151, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2715 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d98 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2716 (p : Pattern) (guard : d1151 p = 1) : d270 p ≤ (0 : Int) + d98 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2712 p hg
    simpa only [d1151, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2715 p hg
    simpa only [d1151, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2717 (p : Pattern) (guard : d1151 p = 1) : d271 p ≤ (0 : Int) + d98 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2714 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2716 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2718 (p : Pattern) (guard : d1151 p = 1) : d272 p ≤ (0 : Int) + d1155 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d272, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2710 p hg
    simpa only [d272, d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d272, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2717 p hg
    simpa only [d272, d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2719 (p : Pattern) (guard : d0 p = 1) : d160 p ≤ (0 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2720 (p : Pattern) (guard : d1151 p = 1) : d273 p ≤ (0 : Int) + d86 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2707 p hg
    simpa only [d1151, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2719 p hg
    simpa only [d1151, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2721 (p : Pattern) (guard : d1151 p = 1) : d274 p ≤ (0 : Int) + d1154 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d274, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2699 p hg
    simpa only [d274, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d274, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2720 p hg
    simpa only [d274, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2722 (p : Pattern) (guard : d0 p = 1) : d97 p ≤ (0 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2723 (p : Pattern) (guard : d1150 p = 1) : d110 p ≤ (0 : Int) + d97 p := by
  cases selected : p 133 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2722 p hg
    simpa only [d1150, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d1150, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1177 p hg
    simpa only [d1150, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2724 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2725 (p : Pattern) (guard : d1151 p = 1) : d275 p ≤ (0 : Int) + d97 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2723 p hg
    simpa only [d1151, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2724 p hg
    simpa only [d1151, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2726 (p : Pattern) (guard : d1151 p = 1) : d276 p ≤ (0 : Int) + d1156 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d276, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2716 p hg
    simpa only [d276, d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d276, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2725 p hg
    simpa only [d276, d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2727 (p : Pattern) (guard : d1151 p = 1) : d277 p ≤ (0 : Int) + d1157 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d277, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2721 p hg
    simpa only [d277, d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d277, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2726 p hg
    simpa only [d277, d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2728 (p : Pattern) (guard : d1151 p = 1) : d278 p ≤ (0 : Int) + d1158 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d278, d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2718 p hg
    simpa only [d278, d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d278, d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2727 p hg
    simpa only [d278, d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2729 (p : Pattern) (guard : d1151 p = 1) : d279 p ≤ (0 : Int) + d1159 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d279, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2705 p hg
    simpa only [d279, d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d279, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2728 p hg
    simpa only [d279, d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2730 (p : Pattern) (guard : d0 p = 1) : d160 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2731 (p : Pattern) (guard : d1151 p = 1) : d280 p ≤ (0 : Int) + d16 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2685 p hg
    simpa only [d1151, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2730 p hg
    simpa only [d1151, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2732 (p : Pattern) (guard : d1151 p = 1) : d281 p ≤ (0 : Int) + d16 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2699 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2731 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2733 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2734 (p : Pattern) (guard : d1151 p = 1) : d282 p ≤ (0 : Int) + d15 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2689 p hg
    simpa only [d1151, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2733 p hg
    simpa only [d1151, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2735 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2736 (p : Pattern) (guard : d1151 p = 1) : d283 p ≤ (0 : Int) + d53 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2693 p hg
    simpa only [d1151, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2735 p hg
    simpa only [d1151, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2737 (p : Pattern) (guard : d1151 p = 1) : d284 p ≤ (0 : Int) + d1152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d284, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2734 p hg
    simpa only [d284, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d284, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2736 p hg
    simpa only [d284, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2738 (p : Pattern) (guard : d1151 p = 1) : d285 p ≤ (0 : Int) + d1153 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d285, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2732 p hg
    simpa only [d285, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d285, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2737 p hg
    simpa only [d285, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2739 (p : Pattern) (guard : d1151 p = 1) : d286 p ≤ (0 : Int) + d1153 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2704 p hg
    simpa only [d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2738 p hg
    simpa only [d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2740 (p : Pattern) (guard : d1151 p = 1) : d287 p ≤ (0 : Int) + d1160 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d287, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2731 p hg
    simpa only [d287, d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d287, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2736 p hg
    simpa only [d287, d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2741 (p : Pattern) (guard : d1151 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare2742 (p : Pattern) (guard : d1151 p = 1) : d288 p ≤ (0 : Int) + d1161 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d288, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2725 p hg
    simpa only [d288, d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d288, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2741 p hg
    simpa only [d288, d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2743 (p : Pattern) (guard : d1151 p = 1) : d289 p ≤ (0 : Int) + d1162 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d289, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2740 p hg
    simpa only [d289, d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d289, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2742 p hg
    simpa only [d289, d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2744 (p : Pattern) (guard : d1151 p = 1) : d290 p ≤ (0 : Int) + d1163 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d290, d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2727 p hg
    simpa only [d290, d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d290, d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2743 p hg
    simpa only [d290, d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2745 (p : Pattern) (guard : d1151 p = 1) : d291 p ≤ (0 : Int) + d1164 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d291, d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2739 p hg
    simpa only [d291, d1164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d291, d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2744 p hg
    simpa only [d291, d1164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2746 (p : Pattern) (guard : d1151 p = 1) : d292 p ≤ (0 : Int) + d1165 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d292, d1165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2729 p hg
    simpa only [d292, d1165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d292, d1165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2745 p hg
    simpa only [d292, d1165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2747 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (0 : Int) + d73 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2748 (p : Pattern) (guard : d841 p = 1) : d256 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d256, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d841, d256, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d256, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2747 p hg
    simpa only [d841, d256, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2749 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d76 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2750 (p : Pattern) (guard : d841 p = 1) : d261 p ≤ (0 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d261, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d841, d261, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d261, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2749 p hg
    simpa only [d841, d261, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2751 (p : Pattern) (guard : d841 p = 1) : d262 p ≤ (0 : Int) + d78 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d262, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2748 p hg
    simpa only [d262, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d262, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2750 p hg
    simpa only [d262, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2752 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2753 (p : Pattern) (guard : d841 p = 1) : d257 p ≤ (0 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d257, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare539 p hg
    simpa only [d841, d257, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d257, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2752 p hg
    simpa only [d841, d257, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2754 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d81 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2755 (p : Pattern) (guard : d841 p = 1) : d263 p ≤ (0 : Int) + d82 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d263, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare542 p hg
    simpa only [d841, d263, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d263, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2754 p hg
    simpa only [d841, d263, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2756 (p : Pattern) (guard : d841 p = 1) : d264 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d264, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2753 p hg
    simpa only [d264, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d264, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2755 p hg
    simpa only [d264, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2757 (p : Pattern) (guard : d841 p = 1) : d265 p ≤ (0 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d265, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2751 p hg
    simpa only [d265, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d265, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2756 p hg
    simpa only [d265, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2758 (p : Pattern) (guard : d841 p = 1) : d266 p ≤ (0 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d266, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d266, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d266, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2757 p hg
    simpa only [d266, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2759 (p : Pattern) (guard : d0 p = 1) : d160 p ≤ (0 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2760 (p : Pattern) (guard : d841 p = 1) : d273 p ≤ (0 : Int) + d105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d273, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare559 p hg
    simpa only [d841, d273, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d273, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2759 p hg
    simpa only [d841, d273, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2761 (p : Pattern) (guard : d841 p = 1) : d274 p ≤ (0 : Int) + d106 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d274, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2750 p hg
    simpa only [d274, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d274, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2760 p hg
    simpa only [d274, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2762 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2763 (p : Pattern) (guard : d841 p = 1) : d270 p ≤ (0 : Int) + d108 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d270, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare563 p hg
    simpa only [d841, d270, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d270, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2762 p hg
    simpa only [d841, d270, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2764 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d111 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2765 (p : Pattern) (guard : d841 p = 1) : d275 p ≤ (0 : Int) + d112 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d275, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare575 p hg
    simpa only [d841, d275, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d275, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2764 p hg
    simpa only [d841, d275, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2766 (p : Pattern) (guard : d841 p = 1) : d276 p ≤ (0 : Int) + d113 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d276, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2763 p hg
    simpa only [d276, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d276, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2765 p hg
    simpa only [d276, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2767 (p : Pattern) (guard : d841 p = 1) : d277 p ≤ (0 : Int) + d114 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d277, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2761 p hg
    simpa only [d277, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d277, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2766 p hg
    simpa only [d277, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2768 (p : Pattern) (guard : d841 p = 1) : d278 p ≤ (0 : Int) + d115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d278, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2510 p hg
    simpa only [d278, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d278, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2767 p hg
    simpa only [d278, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2769 (p : Pattern) (guard : d841 p = 1) : d279 p ≤ (0 : Int) + d116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d279, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2758 p hg
    simpa only [d279, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d279, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2768 p hg
    simpa only [d279, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2770 (p : Pattern) (guard : d0 p = 1) : d160 p ≤ (0 : Int) + d76 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2771 (p : Pattern) (guard : d841 p = 1) : d280 p ≤ (0 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d280, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d841, d280, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d280, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2770 p hg
    simpa only [d841, d280, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2772 (p : Pattern) (guard : d841 p = 1) : d281 p ≤ (0 : Int) + d77 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2750 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2771 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2773 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2774 (p : Pattern) (guard : d841 p = 1) : d282 p ≤ (0 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d282, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare539 p hg
    simpa only [d841, d282, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d282, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2773 p hg
    simpa only [d841, d282, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2775 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d81 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2776 (p : Pattern) (guard : d841 p = 1) : d283 p ≤ (0 : Int) + d82 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d283, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare542 p hg
    simpa only [d841, d283, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d283, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2775 p hg
    simpa only [d841, d283, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2777 (p : Pattern) (guard : d841 p = 1) : d284 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d284, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2774 p hg
    simpa only [d284, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d284, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2776 p hg
    simpa only [d284, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2778 (p : Pattern) (guard : d841 p = 1) : d285 p ≤ (0 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d285, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2772 p hg
    simpa only [d285, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d285, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2777 p hg
    simpa only [d285, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2779 (p : Pattern) (guard : d841 p = 1) : d286 p ≤ (0 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d286, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2520 p hg
    simpa only [d286, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d286, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2778 p hg
    simpa only [d286, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2780 (p : Pattern) (guard : d841 p = 1) : d287 p ≤ (0 : Int) + d129 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d287, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2771 p hg
    simpa only [d287, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d287, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2776 p hg
    simpa only [d287, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2781 (p : Pattern) (guard : d841 p = 1) : d288 p ≤ (0 : Int) + d130 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d288, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2765 p hg
    simpa only [d288, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d288, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare607 p hg
    simpa only [d288, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2782 (p : Pattern) (guard : d841 p = 1) : d289 p ≤ (0 : Int) + d131 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d289, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2780 p hg
    simpa only [d289, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d289, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2781 p hg
    simpa only [d289, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2783 (p : Pattern) (guard : d841 p = 1) : d290 p ≤ (0 : Int) + d132 p := by
  cases selected : p 106 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d290, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d290, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d290, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2782 p hg
    simpa only [d290, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2784 (p : Pattern) (guard : d841 p = 1) : d291 p ≤ (0 : Int) + d133 p := by
  cases selected : p 86 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d291, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2779 p hg
    simpa only [d291, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d291, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2783 p hg
    simpa only [d291, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2785 (p : Pattern) (guard : d841 p = 1) : d292 p ≤ (0 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d292, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2769 p hg
    simpa only [d292, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d292, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2784 p hg
    simpa only [d292, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2786 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2787 (p : Pattern) (guard : d1167 p = 1) : d6 p ≤ (0 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d6, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d1167, d6, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d6, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2786 p hg
    simpa only [d1167, d6, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2788 (p : Pattern) (guard : d1167 p = 1) : d7 p ≤ (0 : Int) + d7 p := by
  omega
theorem compare2789 (p : Pattern) (guard : d1167 p = 1) : d8 p ≤ (0 : Int) + d7 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2787 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2788 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2790 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2791 (p : Pattern) (guard : d1167 p = 1) : d12 p ≤ (0 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare665 p hg
    simpa only [d1167, d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2790 p hg
    simpa only [d1167, d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2792 (p : Pattern) (guard : d1167 p = 1) : d13 p ≤ (0 : Int) + d13 p := by
  omega
theorem compare2793 (p : Pattern) (guard : d1167 p = 1) : d14 p ≤ (0 : Int) + d13 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2791 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2792 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2794 (p : Pattern) (guard : d1167 p = 1) : d15 p ≤ (0 : Int) + d653 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d15, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2789 p hg
    simpa only [d15, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d15, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2793 p hg
    simpa only [d15, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2795 (p : Pattern) (guard : d1167 p = 1) : d16 p ≤ (0 : Int) + d654 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d16, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2789 p hg
    simpa only [d16, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d16, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2794 p hg
    simpa only [d16, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2796 (p : Pattern) (guard : d1171 p = 1) : d8 p ≤ (0 : Int) + d7 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2787 p hg
    simpa only [d1171, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare663 p hg
    simpa only [d1171, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2797 (p : Pattern) (guard : d1171 p = 1) : d14 p ≤ (0 : Int) + d13 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2791 p hg
    simpa only [d1171, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare668 p hg
    simpa only [d1171, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2798 (p : Pattern) (guard : d1171 p = 1) : d15 p ≤ (0 : Int) + d653 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d15, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2796 p hg
    simpa only [d15, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d15, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2797 p hg
    simpa only [d15, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2799 (p : Pattern) (guard : d1171 p = 1) : d16 p ≤ (0 : Int) + d654 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d16, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2796 p hg
    simpa only [d16, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d16, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2798 p hg
    simpa only [d16, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
