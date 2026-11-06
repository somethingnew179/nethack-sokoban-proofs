/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2800 (p : Pattern) (guard : d0 p = 1) : d17 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2801 (p : Pattern) (guard : d1167 p = 1) : d18 p ≤ (0 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d18, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d1167, d18, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d18, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2800 p hg
    simpa only [d1167, d18, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2802 (p : Pattern) (guard : d1171 p = 1) : d20 p ≤ (0 : Int) + d7 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2801 p hg
    simpa only [d1171, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare762 p hg
    simpa only [d1171, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2803 (p : Pattern) (guard : d0 p = 1) : d21 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2804 (p : Pattern) (guard : d1167 p = 1) : d22 p ≤ (0 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d22, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare665 p hg
    simpa only [d1167, d22, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d22, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2803 p hg
    simpa only [d1167, d22, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2805 (p : Pattern) (guard : d1171 p = 1) : d24 p ≤ (0 : Int) + d13 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2804 p hg
    simpa only [d1171, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare680 p hg
    simpa only [d1171, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2806 (p : Pattern) (guard : d1171 p = 1) : d25 p ≤ (0 : Int) + d653 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d25, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2802 p hg
    simpa only [d25, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d25, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2805 p hg
    simpa only [d25, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2807 (p : Pattern) (guard : d1171 p = 1) : d26 p ≤ (0 : Int) + d654 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d26, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2802 p hg
    simpa only [d26, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d26, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2806 p hg
    simpa only [d26, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2808 (p : Pattern) (guard : d1171 p = 1) : d27 p ≤ (0 : Int) + d654 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2799 p hg
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2807 p hg
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2809 (p : Pattern) (guard : d1172 p = 1) : d28 p ≤ (0 : Int) + d654 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1172, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2795 p hg
    simpa only [d1172, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d1172, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2808 p hg
    simpa only [d1172, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2810 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (0 : Int) + d654 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2811 (p : Pattern) (guard : d1173 p = 1) : d256 p ≤ (0 : Int) + d654 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2809 p hg
    simpa only [d1173, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2810 p hg
    simpa only [d1173, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2812 (p : Pattern) (guard : d1171 p = 1) : d46 p ≤ (0 : Int) + d653 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2798 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2806 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2813 (p : Pattern) (guard : d1172 p = 1) : d47 p ≤ (0 : Int) + d653 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1172, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2794 p hg
    simpa only [d1172, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d1172, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2812 p hg
    simpa only [d1172, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2814 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d653 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2815 (p : Pattern) (guard : d1173 p = 1) : d257 p ≤ (0 : Int) + d653 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2813 p hg
    simpa only [d1173, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2814 p hg
    simpa only [d1173, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2816 (p : Pattern) (guard : d1167 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare2817 (p : Pattern) (guard : d1167 p = 1) : d52 p ≤ (0 : Int) + d655 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d52, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2789 p hg
    simpa only [d52, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d52, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2816 p hg
    simpa only [d52, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2818 (p : Pattern) (guard : d1167 p = 1) : d53 p ≤ (0 : Int) + d656 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d53, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2794 p hg
    simpa only [d53, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d53, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2817 p hg
    simpa only [d53, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2819 (p : Pattern) (guard : d1171 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare2820 (p : Pattern) (guard : d1171 p = 1) : d52 p ≤ (0 : Int) + d655 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d52, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2796 p hg
    simpa only [d52, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d52, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d52, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2821 (p : Pattern) (guard : d1171 p = 1) : d53 p ≤ (0 : Int) + d656 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d53, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2798 p hg
    simpa only [d53, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d53, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2820 p hg
    simpa only [d53, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2822 (p : Pattern) (guard : d1171 p = 1) : d54 p ≤ (0 : Int) + d655 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d54, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2802 p hg
    simpa only [d54, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d54, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d54, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2823 (p : Pattern) (guard : d1171 p = 1) : d55 p ≤ (0 : Int) + d656 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d55, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2806 p hg
    simpa only [d55, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d55, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2822 p hg
    simpa only [d55, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2824 (p : Pattern) (guard : d1171 p = 1) : d56 p ≤ (0 : Int) + d656 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2821 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2823 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2825 (p : Pattern) (guard : d1172 p = 1) : d57 p ≤ (0 : Int) + d656 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1172, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2818 p hg
    simpa only [d1172, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d1172, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2824 p hg
    simpa only [d1172, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2826 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d656 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2827 (p : Pattern) (guard : d1173 p = 1) : d258 p ≤ (0 : Int) + d656 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2825 p hg
    simpa only [d1173, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2826 p hg
    simpa only [d1173, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2828 (p : Pattern) (guard : d1173 p = 1) : d259 p ≤ (0 : Int) + d657 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d259, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2815 p hg
    simpa only [d259, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d259, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2827 p hg
    simpa only [d259, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2829 (p : Pattern) (guard : d1173 p = 1) : d260 p ≤ (0 : Int) + d658 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d260, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2811 p hg
    simpa only [d260, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d260, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2828 p hg
    simpa only [d260, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2830 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (0 : Int) + d661 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2831 (p : Pattern) (guard : d1173 p = 1) : d256 p ≤ (0 : Int) + d662 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d256, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2809 p hg
    simpa only [d1173, d256, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d256, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2830 p hg
    simpa only [d1173, d256, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2832 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d663 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2833 (p : Pattern) (guard : d1173 p = 1) : d261 p ≤ (0 : Int) + d664 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d261, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2809 p hg
    simpa only [d1173, d261, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d261, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2832 p hg
    simpa only [d1173, d261, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2834 (p : Pattern) (guard : d1173 p = 1) : d262 p ≤ (0 : Int) + d665 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d262, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2831 p hg
    simpa only [d262, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d262, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2833 p hg
    simpa only [d262, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2835 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d666 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2836 (p : Pattern) (guard : d1173 p = 1) : d257 p ≤ (0 : Int) + d667 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d257, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2813 p hg
    simpa only [d1173, d257, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d257, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2835 p hg
    simpa only [d1173, d257, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2837 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d668 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2838 (p : Pattern) (guard : d1173 p = 1) : d263 p ≤ (0 : Int) + d669 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d263, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2825 p hg
    simpa only [d1173, d263, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d263, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2837 p hg
    simpa only [d1173, d263, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2839 (p : Pattern) (guard : d1173 p = 1) : d264 p ≤ (0 : Int) + d670 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d264, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2836 p hg
    simpa only [d264, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d264, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2838 p hg
    simpa only [d264, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2840 (p : Pattern) (guard : d1173 p = 1) : d265 p ≤ (0 : Int) + d671 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d265, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2834 p hg
    simpa only [d265, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d265, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2839 p hg
    simpa only [d265, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2841 (p : Pattern) (guard : d1173 p = 1) : d266 p ≤ (0 : Int) + d672 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d266, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2829 p hg
    simpa only [d266, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d266, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2840 p hg
    simpa only [d266, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2842 (p : Pattern) (guard : d1167 p = 1) : d86 p ≤ (0 : Int) + d673 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d86, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2789 p hg
    simpa only [d86, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d86, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2817 p hg
    simpa only [d86, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2843 (p : Pattern) (guard : d1171 p = 1) : d86 p ≤ (0 : Int) + d673 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d86, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2796 p hg
    simpa only [d86, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d86, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2820 p hg
    simpa only [d86, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2844 (p : Pattern) (guard : d1171 p = 1) : d87 p ≤ (0 : Int) + d673 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d87, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2802 p hg
    simpa only [d87, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d87, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2822 p hg
    simpa only [d87, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2845 (p : Pattern) (guard : d1171 p = 1) : d88 p ≤ (0 : Int) + d673 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2843 p hg
    simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2844 p hg
    simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2846 (p : Pattern) (guard : d1172 p = 1) : d89 p ≤ (0 : Int) + d673 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1172, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2842 p hg
    simpa only [d1172, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d1172, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2845 p hg
    simpa only [d1172, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2847 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d673 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2848 (p : Pattern) (guard : d1173 p = 1) : d267 p ≤ (0 : Int) + d673 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2846 p hg
    simpa only [d1173, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2847 p hg
    simpa only [d1173, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2849 (p : Pattern) (guard : d1173 p = 1) : d268 p ≤ (0 : Int) + d674 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d268, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2811 p hg
    simpa only [d268, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d268, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2848 p hg
    simpa only [d268, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2850 (p : Pattern) (guard : d1167 p = 1) : d97 p ≤ (0 : Int) + d659 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d97, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2793 p hg
    simpa only [d97, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d97, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2816 p hg
    simpa only [d97, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2851 (p : Pattern) (guard : d1167 p = 1) : d98 p ≤ (0 : Int) + d660 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d98, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2793 p hg
    simpa only [d98, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d98, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2850 p hg
    simpa only [d98, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2852 (p : Pattern) (guard : d1171 p = 1) : d97 p ≤ (0 : Int) + d659 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d97, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2797 p hg
    simpa only [d97, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d97, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d97, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2853 (p : Pattern) (guard : d1171 p = 1) : d98 p ≤ (0 : Int) + d660 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d98, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2797 p hg
    simpa only [d98, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d98, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2852 p hg
    simpa only [d98, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2854 (p : Pattern) (guard : d1171 p = 1) : d70 p ≤ (0 : Int) + d659 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d70, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2805 p hg
    simpa only [d70, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d70, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d70, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2855 (p : Pattern) (guard : d1171 p = 1) : d71 p ≤ (0 : Int) + d660 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d71, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2805 p hg
    simpa only [d71, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d71, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2854 p hg
    simpa only [d71, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2856 (p : Pattern) (guard : d1171 p = 1) : d99 p ≤ (0 : Int) + d660 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2853 p hg
    simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2855 p hg
    simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2857 (p : Pattern) (guard : d1172 p = 1) : d100 p ≤ (0 : Int) + d660 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1172, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2851 p hg
    simpa only [d1172, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d1172, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2856 p hg
    simpa only [d1172, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2858 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d660 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2859 (p : Pattern) (guard : d1173 p = 1) : d269 p ≤ (0 : Int) + d660 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2857 p hg
    simpa only [d1173, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2858 p hg
    simpa only [d1173, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2860 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d660 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2861 (p : Pattern) (guard : d1173 p = 1) : d270 p ≤ (0 : Int) + d660 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2857 p hg
    simpa only [d1173, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2860 p hg
    simpa only [d1173, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2862 (p : Pattern) (guard : d1173 p = 1) : d271 p ≤ (0 : Int) + d660 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2859 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2861 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2863 (p : Pattern) (guard : d1173 p = 1) : d272 p ≤ (0 : Int) + d675 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d272, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2849 p hg
    simpa only [d272, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d272, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2862 p hg
    simpa only [d272, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2864 (p : Pattern) (guard : d0 p = 1) : d160 p ≤ (0 : Int) + d676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2865 (p : Pattern) (guard : d1173 p = 1) : d273 p ≤ (0 : Int) + d677 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d273, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2846 p hg
    simpa only [d1173, d273, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d273, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2864 p hg
    simpa only [d1173, d273, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2866 (p : Pattern) (guard : d1173 p = 1) : d274 p ≤ (0 : Int) + d678 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d274, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2833 p hg
    simpa only [d274, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d274, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2865 p hg
    simpa only [d274, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2867 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d679 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2868 (p : Pattern) (guard : d1173 p = 1) : d270 p ≤ (0 : Int) + d680 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d270, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2857 p hg
    simpa only [d1173, d270, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d270, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2867 p hg
    simpa only [d1173, d270, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2869 (p : Pattern) (guard : d1171 p = 1) : d109 p ≤ (0 : Int) + d659 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2852 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2854 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2870 (p : Pattern) (guard : d1172 p = 1) : d110 p ≤ (0 : Int) + d659 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1172, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2850 p hg
    simpa only [d1172, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d1172, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2869 p hg
    simpa only [d1172, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2871 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d681 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2872 (p : Pattern) (guard : d1173 p = 1) : d275 p ≤ (0 : Int) + d682 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d275, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2870 p hg
    simpa only [d1173, d275, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d275, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2871 p hg
    simpa only [d1173, d275, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2873 (p : Pattern) (guard : d1173 p = 1) : d276 p ≤ (0 : Int) + d683 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d276, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2868 p hg
    simpa only [d276, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d276, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2872 p hg
    simpa only [d276, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2874 (p : Pattern) (guard : d1173 p = 1) : d277 p ≤ (0 : Int) + d684 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d277, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2866 p hg
    simpa only [d277, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d277, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2873 p hg
    simpa only [d277, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2875 (p : Pattern) (guard : d1173 p = 1) : d278 p ≤ (0 : Int) + d685 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d278, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2863 p hg
    simpa only [d278, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d278, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2874 p hg
    simpa only [d278, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2876 (p : Pattern) (guard : d1173 p = 1) : d279 p ≤ (0 : Int) + d686 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d279, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2841 p hg
    simpa only [d279, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d279, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2875 p hg
    simpa only [d279, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2877 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d654 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2878 (p : Pattern) (guard : d1173 p = 1) : d261 p ≤ (0 : Int) + d654 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2809 p hg
    simpa only [d1173, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2877 p hg
    simpa only [d1173, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2879 (p : Pattern) (guard : d1173 p = 1) : d262 p ≤ (0 : Int) + d654 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2811 p hg
    simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2878 p hg
    simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2880 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d656 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2881 (p : Pattern) (guard : d1173 p = 1) : d263 p ≤ (0 : Int) + d656 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2825 p hg
    simpa only [d1173, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2880 p hg
    simpa only [d1173, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2882 (p : Pattern) (guard : d1173 p = 1) : d264 p ≤ (0 : Int) + d657 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d264, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2815 p hg
    simpa only [d264, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d264, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2881 p hg
    simpa only [d264, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2883 (p : Pattern) (guard : d1173 p = 1) : d265 p ≤ (0 : Int) + d658 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d265, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2879 p hg
    simpa only [d265, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d265, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2882 p hg
    simpa only [d265, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2884 (p : Pattern) (guard : d0 p = 1) : d160 p ≤ (0 : Int) + d663 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2885 (p : Pattern) (guard : d1173 p = 1) : d280 p ≤ (0 : Int) + d664 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d280, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2809 p hg
    simpa only [d1173, d280, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d280, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2884 p hg
    simpa only [d1173, d280, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2886 (p : Pattern) (guard : d1173 p = 1) : d281 p ≤ (0 : Int) + d664 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2833 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2885 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2887 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d666 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2888 (p : Pattern) (guard : d1173 p = 1) : d282 p ≤ (0 : Int) + d667 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d282, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2813 p hg
    simpa only [d1173, d282, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d282, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2887 p hg
    simpa only [d1173, d282, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2889 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d668 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2890 (p : Pattern) (guard : d1173 p = 1) : d283 p ≤ (0 : Int) + d669 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d283, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2825 p hg
    simpa only [d1173, d283, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d283, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2889 p hg
    simpa only [d1173, d283, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2891 (p : Pattern) (guard : d1173 p = 1) : d284 p ≤ (0 : Int) + d670 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d284, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2888 p hg
    simpa only [d284, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d284, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2890 p hg
    simpa only [d284, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2892 (p : Pattern) (guard : d1173 p = 1) : d285 p ≤ (0 : Int) + d687 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d285, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2886 p hg
    simpa only [d285, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d285, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2891 p hg
    simpa only [d285, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2893 (p : Pattern) (guard : d1173 p = 1) : d286 p ≤ (0 : Int) + d688 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d286, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2883 p hg
    simpa only [d286, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d286, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2892 p hg
    simpa only [d286, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2894 (p : Pattern) (guard : d0 p = 1) : d160 p ≤ (0 : Int) + d673 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2895 (p : Pattern) (guard : d1173 p = 1) : d273 p ≤ (0 : Int) + d673 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2846 p hg
    simpa only [d1173, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2894 p hg
    simpa only [d1173, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2896 (p : Pattern) (guard : d1173 p = 1) : d274 p ≤ (0 : Int) + d674 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d274, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2878 p hg
    simpa only [d274, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d274, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2895 p hg
    simpa only [d274, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2897 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d659 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2898 (p : Pattern) (guard : d1173 p = 1) : d275 p ≤ (0 : Int) + d659 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2870 p hg
    simpa only [d1173, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d1173, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2899 (p : Pattern) (guard : d1173 p = 1) : d276 p ≤ (0 : Int) + d689 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d276, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2861 p hg
    simpa only [d276, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d276, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2898 p hg
    simpa only [d276, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2900 (p : Pattern) (guard : d1173 p = 1) : d277 p ≤ (0 : Int) + d690 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d277, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2896 p hg
    simpa only [d277, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d277, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2899 p hg
    simpa only [d277, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2901 (p : Pattern) (guard : d1173 p = 1) : d287 p ≤ (0 : Int) + d691 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d287, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2885 p hg
    simpa only [d287, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d287, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2890 p hg
    simpa only [d287, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2902 (p : Pattern) (guard : d1173 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare2903 (p : Pattern) (guard : d1173 p = 1) : d288 p ≤ (0 : Int) + d692 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d288, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2872 p hg
    simpa only [d288, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d288, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2902 p hg
    simpa only [d288, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2904 (p : Pattern) (guard : d1173 p = 1) : d289 p ≤ (0 : Int) + d693 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d289, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2901 p hg
    simpa only [d289, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d289, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2903 p hg
    simpa only [d289, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2905 (p : Pattern) (guard : d1173 p = 1) : d290 p ≤ (0 : Int) + d694 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d290, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2900 p hg
    simpa only [d290, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d290, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2904 p hg
    simpa only [d290, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2906 (p : Pattern) (guard : d1173 p = 1) : d291 p ≤ (0 : Int) + d695 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d291, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2893 p hg
    simpa only [d291, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d291, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2905 p hg
    simpa only [d291, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2907 (p : Pattern) (guard : d1173 p = 1) : d292 p ≤ (0 : Int) + d696 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d292, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2876 p hg
    simpa only [d292, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d292, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2906 p hg
    simpa only [d292, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2908 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d654 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2909 (p : Pattern) (guard : d1174 p = 1) : d293 p ≤ (0 : Int) + d654 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2795 p hg
    simpa only [d1174, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2908 p hg
    simpa only [d1174, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2910 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d653 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2911 (p : Pattern) (guard : d1174 p = 1) : d294 p ≤ (0 : Int) + d653 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2794 p hg
    simpa only [d1174, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2910 p hg
    simpa only [d1174, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2912 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d656 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2913 (p : Pattern) (guard : d1174 p = 1) : d295 p ≤ (0 : Int) + d656 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2818 p hg
    simpa only [d1174, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2912 p hg
    simpa only [d1174, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2914 (p : Pattern) (guard : d1174 p = 1) : d296 p ≤ (0 : Int) + d657 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d296, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2911 p hg
    simpa only [d296, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d296, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2913 p hg
    simpa only [d296, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2915 (p : Pattern) (guard : d1174 p = 1) : d297 p ≤ (0 : Int) + d658 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d297, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2909 p hg
    simpa only [d297, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d297, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2914 p hg
    simpa only [d297, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2916 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d660 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2917 (p : Pattern) (guard : d1174 p = 1) : d293 p ≤ (0 : Int) + d661 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d293, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2795 p hg
    simpa only [d1174, d293, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d293, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2916 p hg
    simpa only [d1174, d293, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2918 (p : Pattern) (guard : d1174 p = 1) : d293 p ≤ (0 : Int) + d662 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2909 p hg
    simpa only [d662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2917 p hg
    simpa only [d662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2919 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d659 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2920 (p : Pattern) (guard : d1174 p = 1) : d298 p ≤ (0 : Int) + d663 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d298, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2795 p hg
    simpa only [d1174, d298, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d298, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2919 p hg
    simpa only [d1174, d298, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2921 (p : Pattern) (guard : d1174 p = 1) : d299 p ≤ (0 : Int) + d664 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d299, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2909 p hg
    simpa only [d299, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d299, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2920 p hg
    simpa only [d299, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2922 (p : Pattern) (guard : d1174 p = 1) : d300 p ≤ (0 : Int) + d665 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d300, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2918 p hg
    simpa only [d300, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d300, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2921 p hg
    simpa only [d300, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2923 (p : Pattern) (guard : d1174 p = 1) : d294 p ≤ (0 : Int) + d666 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d294, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2794 p hg
    simpa only [d1174, d294, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d294, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d1174, d294, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2924 (p : Pattern) (guard : d1174 p = 1) : d294 p ≤ (0 : Int) + d667 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2911 p hg
    simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2923 p hg
    simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2925 (p : Pattern) (guard : d1174 p = 1) : d295 p ≤ (0 : Int) + d668 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d295, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2818 p hg
    simpa only [d1174, d295, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d295, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d1174, d295, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2926 (p : Pattern) (guard : d1174 p = 1) : d295 p ≤ (0 : Int) + d669 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2913 p hg
    simpa only [d669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2925 p hg
    simpa only [d669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2927 (p : Pattern) (guard : d1174 p = 1) : d296 p ≤ (0 : Int) + d670 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d296, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2924 p hg
    simpa only [d296, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d296, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2926 p hg
    simpa only [d296, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2928 (p : Pattern) (guard : d1174 p = 1) : d301 p ≤ (0 : Int) + d671 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d301, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2922 p hg
    simpa only [d301, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d301, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d301, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2929 (p : Pattern) (guard : d1174 p = 1) : d302 p ≤ (0 : Int) + d672 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d302, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2915 p hg
    simpa only [d302, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d302, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2928 p hg
    simpa only [d302, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2930 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d673 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2931 (p : Pattern) (guard : d1174 p = 1) : d303 p ≤ (0 : Int) + d673 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2842 p hg
    simpa only [d1174, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2930 p hg
    simpa only [d1174, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2932 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d673 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2933 (p : Pattern) (guard : d1174 p = 1) : d304 p ≤ (0 : Int) + d673 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2842 p hg
    simpa only [d1174, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2932 p hg
    simpa only [d1174, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2934 (p : Pattern) (guard : d1174 p = 1) : d305 p ≤ (0 : Int) + d673 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2931 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2933 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2935 (p : Pattern) (guard : d1174 p = 1) : d306 p ≤ (0 : Int) + d674 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d306, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2909 p hg
    simpa only [d306, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d306, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2934 p hg
    simpa only [d306, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2936 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d660 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2937 (p : Pattern) (guard : d1174 p = 1) : d307 p ≤ (0 : Int) + d660 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2851 p hg
    simpa only [d1174, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2936 p hg
    simpa only [d1174, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2938 (p : Pattern) (guard : d1174 p = 1) : d308 p ≤ (0 : Int) + d675 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d308, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2935 p hg
    simpa only [d308, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d308, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2937 p hg
    simpa only [d308, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2939 (p : Pattern) (guard : d1174 p = 1) : d309 p ≤ (0 : Int) + d676 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d309, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2842 p hg
    simpa only [d1174, d309, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d309, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d1174, d309, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
