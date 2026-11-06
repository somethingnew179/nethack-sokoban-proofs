/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2800 (p : Pattern) (guard : d0 p = 1) : d75 p ≤ (0 : Int) + d396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2801 (p : Pattern) (guard : d4117 p = 1) : d76 p ≤ (0 : Int) + d724 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d76, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d76, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d76, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2800 p hg
    simpa only [d4117, d76, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2802 (p : Pattern) (guard : d4117 p = 1) : d77 p ≤ (0 : Int) + d725 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d77, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2799 p hg
    simpa only [d77, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d77, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2801 p hg
    simpa only [d77, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2803 (p : Pattern) (guard : d0 p = 1) : d422 p ≤ (0 : Int) + d727 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2804 (p : Pattern) (guard : d4203 p = 1) : d546 p ≤ (0 : Int) + d728 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d546, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2802 p hg
    simpa only [d4203, d546, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d546, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2803 p hg
    simpa only [d4203, d546, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2805 (p : Pattern) (guard : d0 p = 1) : d530 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2806 (p : Pattern) (guard : d4117 p = 1) : d531 p ≤ (0 : Int) + d726 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d531, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d531, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d531, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2805 p hg
    simpa only [d4117, d531, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2807 (p : Pattern) (guard : d4117 p = 1) : d543 p ≤ (0 : Int) + d727 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d543, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2806 p hg
    simpa only [d543, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d543, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2793 p hg
    simpa only [d543, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2808 (p : Pattern) (guard : d4203 p = 1) : d547 p ≤ (0 : Int) + d729 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d547, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2807 p hg
    simpa only [d4203, d547, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d547, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4203, d547, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2809 (p : Pattern) (guard : d4203 p = 1) : d548 p ≤ (0 : Int) + d730 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d548, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2804 p hg
    simpa only [d548, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d548, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2808 p hg
    simpa only [d548, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2810 (p : Pattern) (guard : d4203 p = 1) : d549 p ≤ (0 : Int) + d731 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d549, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2797 p hg
    simpa only [d549, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d549, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2809 p hg
    simpa only [d549, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2811 (p : Pattern) (guard : d0 p = 1) : d51 p ≤ (0 : Int) + d398 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2812 (p : Pattern) (guard : d4117 p = 1) : d52 p ≤ (0 : Int) + d732 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d52, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d52, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d52, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2811 p hg
    simpa only [d4117, d52, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2813 (p : Pattern) (guard : d0 p = 1) : d75 p ≤ (0 : Int) + d409 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2814 (p : Pattern) (guard : d4117 p = 1) : d76 p ≤ (0 : Int) + d733 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d76, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d76, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d76, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2813 p hg
    simpa only [d4117, d76, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2815 (p : Pattern) (guard : d4117 p = 1) : d77 p ≤ (0 : Int) + d734 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d77, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2812 p hg
    simpa only [d77, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d77, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2814 p hg
    simpa only [d77, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2816 (p : Pattern) (guard : d0 p = 1) : d439 p ≤ (0 : Int) + d727 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2817 (p : Pattern) (guard : d4203 p = 1) : d550 p ≤ (0 : Int) + d735 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d550, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2815 p hg
    simpa only [d4203, d550, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d550, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2816 p hg
    simpa only [d4203, d550, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2818 (p : Pattern) (guard : d0 p = 1) : d530 p ≤ (0 : Int) + d396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2819 (p : Pattern) (guard : d4117 p = 1) : d531 p ≤ (0 : Int) + d713 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d531, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d531, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d531, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2818 p hg
    simpa only [d4117, d531, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2820 (p : Pattern) (guard : d4117 p = 1) : d543 p ≤ (0 : Int) + d715 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d543, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d543, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d543, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2793 p hg
    simpa only [d543, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2821 (p : Pattern) (guard : d0 p = 1) : d441 p ≤ (0 : Int) + d720 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2822 (p : Pattern) (guard : d4203 p = 1) : d551 p ≤ (0 : Int) + d736 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d551, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2820 p hg
    simpa only [d4203, d551, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d551, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2821 p hg
    simpa only [d4203, d551, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2823 (p : Pattern) (guard : d4203 p = 1) : d552 p ≤ (0 : Int) + d737 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d552, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2817 p hg
    simpa only [d552, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d552, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2822 p hg
    simpa only [d552, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2824 (p : Pattern) (guard : d0 p = 1) : d51 p ≤ (0 : Int) + d405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2825 (p : Pattern) (guard : d4117 p = 1) : d52 p ≤ (0 : Int) + d717 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d52, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d52, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d52, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2824 p hg
    simpa only [d4117, d52, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2826 (p : Pattern) (guard : d0 p = 1) : d75 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2827 (p : Pattern) (guard : d4117 p = 1) : d76 p ≤ (0 : Int) + d714 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d76, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d76, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d76, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2826 p hg
    simpa only [d4117, d76, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2828 (p : Pattern) (guard : d4117 p = 1) : d77 p ≤ (0 : Int) + d718 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d77, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2825 p hg
    simpa only [d77, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d77, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2827 p hg
    simpa only [d77, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2829 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d727 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2830 (p : Pattern) (guard : d4203 p = 1) : d553 p ≤ (0 : Int) + d738 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d553, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2828 p hg
    simpa only [d4203, d553, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d553, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2829 p hg
    simpa only [d4203, d553, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2831 (p : Pattern) (guard : d4203 p = 1) : d554 p ≤ (0 : Int) + d739 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d554, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2830 p hg
    simpa only [d554, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d554, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2808 p hg
    simpa only [d554, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2832 (p : Pattern) (guard : d4203 p = 1) : d555 p ≤ (0 : Int) + d740 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d555, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2823 p hg
    simpa only [d555, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d555, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2831 p hg
    simpa only [d555, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2833 (p : Pattern) (guard : d4203 p = 1) : d556 p ≤ (0 : Int) + d741 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d556, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2810 p hg
    simpa only [d556, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d556, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2832 p hg
    simpa only [d556, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2834 (p : Pattern) (guard : d0 p = 1) : d130 p ≤ (0 : Int) + d398 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2835 (p : Pattern) (guard : d4117 p = 1) : d131 p ≤ (0 : Int) + d742 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d131, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d131, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d131, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2834 p hg
    simpa only [d4117, d131, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2836 (p : Pattern) (guard : d0 p = 1) : d145 p ≤ (0 : Int) + d409 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2837 (p : Pattern) (guard : d4117 p = 1) : d146 p ≤ (0 : Int) + d743 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d146, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1570 p hg
    simpa only [d4117, d146, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d146, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2836 p hg
    simpa only [d4117, d146, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2838 (p : Pattern) (guard : d4117 p = 1) : d147 p ≤ (0 : Int) + d744 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d147, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2835 p hg
    simpa only [d147, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d147, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2837 p hg
    simpa only [d147, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2839 (p : Pattern) (guard : d0 p = 1) : d439 p ≤ (0 : Int) + d747 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2840 (p : Pattern) (guard : d4203 p = 1) : d557 p ≤ (0 : Int) + d748 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d557, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2838 p hg
    simpa only [d4203, d557, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d557, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2839 p hg
    simpa only [d4203, d557, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2841 (p : Pattern) (guard : d0 p = 1) : d568 p ≤ (0 : Int) + d396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2842 (p : Pattern) (guard : d4117 p = 1) : d569 p ≤ (0 : Int) + d749 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d569, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d569, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d569, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2841 p hg
    simpa only [d4117, d569, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2843 (p : Pattern) (guard : d0 p = 1) : d577 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2844 (p : Pattern) (guard : d4117 p = 1) : d578 p ≤ (0 : Int) + d746 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d578, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1570 p hg
    simpa only [d4117, d578, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d578, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2843 p hg
    simpa only [d4117, d578, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2845 (p : Pattern) (guard : d4117 p = 1) : d579 p ≤ (0 : Int) + d750 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d579, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2842 p hg
    simpa only [d579, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d579, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2844 p hg
    simpa only [d579, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2846 (p : Pattern) (guard : d0 p = 1) : d441 p ≤ (0 : Int) + d162 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2847 (p : Pattern) (guard : d4203 p = 1) : d580 p ≤ (0 : Int) + d751 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d580, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2845 p hg
    simpa only [d4203, d580, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d580, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2846 p hg
    simpa only [d4203, d580, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2848 (p : Pattern) (guard : d4203 p = 1) : d581 p ≤ (0 : Int) + d752 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d581, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2840 p hg
    simpa only [d581, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d581, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2847 p hg
    simpa only [d581, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2849 (p : Pattern) (guard : d0 p = 1) : d130 p ≤ (0 : Int) + d405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2850 (p : Pattern) (guard : d4117 p = 1) : d131 p ≤ (0 : Int) + d753 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d131, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d131, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d131, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2849 p hg
    simpa only [d4117, d131, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2851 (p : Pattern) (guard : d0 p = 1) : d145 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2852 (p : Pattern) (guard : d4117 p = 1) : d146 p ≤ (0 : Int) + d746 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d146, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1570 p hg
    simpa only [d4117, d146, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d146, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2851 p hg
    simpa only [d4117, d146, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2853 (p : Pattern) (guard : d4117 p = 1) : d147 p ≤ (0 : Int) + d754 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d147, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2850 p hg
    simpa only [d147, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d147, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2852 p hg
    simpa only [d147, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2854 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d747 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2855 (p : Pattern) (guard : d4203 p = 1) : d582 p ≤ (0 : Int) + d755 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d582, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2853 p hg
    simpa only [d4203, d582, d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d582, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2854 p hg
    simpa only [d4203, d582, d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2856 (p : Pattern) (guard : d0 p = 1) : d568 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2857 (p : Pattern) (guard : d4117 p = 1) : d569 p ≤ (0 : Int) + d745 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d569, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d569, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d569, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2856 p hg
    simpa only [d4117, d569, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2858 (p : Pattern) (guard : d4117 p = 1) : d579 p ≤ (0 : Int) + d747 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d579, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2857 p hg
    simpa only [d579, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d579, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2844 p hg
    simpa only [d579, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2859 (p : Pattern) (guard : d4203 p = 1) : d583 p ≤ (0 : Int) + d756 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d583, d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2858 p hg
    simpa only [d4203, d583, d756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d583, d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4203, d583, d756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2860 (p : Pattern) (guard : d4203 p = 1) : d584 p ≤ (0 : Int) + d757 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d584, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2855 p hg
    simpa only [d584, d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d584, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2859 p hg
    simpa only [d584, d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2861 (p : Pattern) (guard : d4203 p = 1) : d585 p ≤ (0 : Int) + d758 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d585, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2848 p hg
    simpa only [d585, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d585, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2860 p hg
    simpa only [d585, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2862 (p : Pattern) (guard : d4203 p = 1) : d586 p ≤ (0 : Int) + d759 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d586, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2810 p hg
    simpa only [d586, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d586, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2861 p hg
    simpa only [d586, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2863 (p : Pattern) (guard : d4203 p = 1) : d587 p ≤ (0 : Int) + d760 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d587, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2833 p hg
    simpa only [d587, d760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d587, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2862 p hg
    simpa only [d587, d760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2864 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d763 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2865 (p : Pattern) (guard : d4203 p = 1) : d553 p ≤ (0 : Int) + d764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d553, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2828 p hg
    simpa only [d4203, d553, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d553, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2864 p hg
    simpa only [d4203, d553, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2866 (p : Pattern) (guard : d1 p = 1) : d189 p ≤ (0 : Int) + d189 p := by
  omega
theorem compare2867 (p : Pattern) (guard : d0 p = 1) : d595 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2868 (p : Pattern) (guard : d4117 p = 1) : d596 p ≤ (0 : Int) + d761 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d596, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2866 p hg
    simpa only [d4117, d596, d761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d596, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2867 p hg
    simpa only [d4117, d596, d761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2869 (p : Pattern) (guard : d1 p = 1) : d200 p ≤ (0 : Int) + d200 p := by
  omega
theorem compare2870 (p : Pattern) (guard : d0 p = 1) : d603 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2871 (p : Pattern) (guard : d4117 p = 1) : d604 p ≤ (0 : Int) + d762 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d604, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2869 p hg
    simpa only [d4117, d604, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d604, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2870 p hg
    simpa only [d4117, d604, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2872 (p : Pattern) (guard : d4117 p = 1) : d605 p ≤ (0 : Int) + d763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d605, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2868 p hg
    simpa only [d605, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d605, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2871 p hg
    simpa only [d605, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2873 (p : Pattern) (guard : d4203 p = 1) : d606 p ≤ (0 : Int) + d765 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d606, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2872 p hg
    simpa only [d4203, d606, d765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d606, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4203, d606, d765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2874 (p : Pattern) (guard : d4203 p = 1) : d607 p ≤ (0 : Int) + d766 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d607, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2865 p hg
    simpa only [d607, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d607, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2873 p hg
    simpa only [d607, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2875 (p : Pattern) (guard : d4203 p = 1) : d608 p ≤ (0 : Int) + d767 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d608, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2823 p hg
    simpa only [d608, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d608, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2874 p hg
    simpa only [d608, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2876 (p : Pattern) (guard : d4203 p = 1) : d609 p ≤ (0 : Int) + d768 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d609, d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2810 p hg
    simpa only [d609, d768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d609, d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2875 p hg
    simpa only [d609, d768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2877 (p : Pattern) (guard : d0 p = 1) : d218 p ≤ (0 : Int) + d409 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2878 (p : Pattern) (guard : d4117 p = 1) : d219 p ≤ (0 : Int) + d769 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d219, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d4117, d219, d769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d219, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2877 p hg
    simpa only [d4117, d219, d769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2879 (p : Pattern) (guard : d4117 p = 1) : d220 p ≤ (0 : Int) + d770 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d220, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2835 p hg
    simpa only [d220, d770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d220, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2878 p hg
    simpa only [d220, d770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2880 (p : Pattern) (guard : d0 p = 1) : d457 p ≤ (0 : Int) + d772 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2881 (p : Pattern) (guard : d4203 p = 1) : d610 p ≤ (0 : Int) + d773 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d610, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2879 p hg
    simpa only [d4203, d610, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d610, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2880 p hg
    simpa only [d4203, d610, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2882 (p : Pattern) (guard : d0 p = 1) : d614 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2883 (p : Pattern) (guard : d4117 p = 1) : d615 p ≤ (0 : Int) + d771 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d615, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d4117, d615, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d615, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2882 p hg
    simpa only [d4117, d615, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2884 (p : Pattern) (guard : d4117 p = 1) : d616 p ≤ (0 : Int) + d774 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d616, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2842 p hg
    simpa only [d616, d774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d616, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2883 p hg
    simpa only [d616, d774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2885 (p : Pattern) (guard : d4203 p = 1) : d617 p ≤ (0 : Int) + d775 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d617, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2884 p hg
    simpa only [d4203, d617, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d617, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2846 p hg
    simpa only [d4203, d617, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2886 (p : Pattern) (guard : d4203 p = 1) : d618 p ≤ (0 : Int) + d776 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d618, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2881 p hg
    simpa only [d618, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d618, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2885 p hg
    simpa only [d618, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2887 (p : Pattern) (guard : d0 p = 1) : d280 p ≤ (0 : Int) + d405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2888 (p : Pattern) (guard : d4117 p = 1) : d281 p ≤ (0 : Int) + d753 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d281, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d281, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d281, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2887 p hg
    simpa only [d4117, d281, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2889 (p : Pattern) (guard : d0 p = 1) : d288 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2890 (p : Pattern) (guard : d4117 p = 1) : d289 p ≤ (0 : Int) + d771 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d289, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d4117, d289, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d289, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2889 p hg
    simpa only [d4117, d289, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2891 (p : Pattern) (guard : d4117 p = 1) : d290 p ≤ (0 : Int) + d777 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d290, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2888 p hg
    simpa only [d290, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d290, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2890 p hg
    simpa only [d290, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2892 (p : Pattern) (guard : d0 p = 1) : d473 p ≤ (0 : Int) + d780 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2893 (p : Pattern) (guard : d4203 p = 1) : d619 p ≤ (0 : Int) + d781 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d619, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2891 p hg
    simpa only [d4203, d619, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d619, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2892 p hg
    simpa only [d4203, d619, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2894 (p : Pattern) (guard : d1 p = 1) : d256 p ≤ (0 : Int) + d256 p := by
  omega
theorem compare2895 (p : Pattern) (guard : d0 p = 1) : d630 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2896 (p : Pattern) (guard : d4117 p = 1) : d631 p ≤ (0 : Int) + d782 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d631, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2894 p hg
    simpa only [d4117, d631, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d631, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2895 p hg
    simpa only [d4117, d631, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2897 (p : Pattern) (guard : d1 p = 1) : d246 p ≤ (0 : Int) + d246 p := by
  omega
theorem compare2898 (p : Pattern) (guard : d0 p = 1) : d644 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2899 (p : Pattern) (guard : d4117 p = 1) : d645 p ≤ (0 : Int) + d779 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d645, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d4117, d645, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d645, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2898 p hg
    simpa only [d4117, d645, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2900 (p : Pattern) (guard : d4117 p = 1) : d646 p ≤ (0 : Int) + d783 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d646, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2896 p hg
    simpa only [d646, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d646, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2899 p hg
    simpa only [d646, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2901 (p : Pattern) (guard : d4203 p = 1) : d647 p ≤ (0 : Int) + d784 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d647, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2900 p hg
    simpa only [d4203, d647, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d647, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4203, d647, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2902 (p : Pattern) (guard : d4203 p = 1) : d648 p ≤ (0 : Int) + d785 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d648, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2893 p hg
    simpa only [d648, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d648, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2901 p hg
    simpa only [d648, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2903 (p : Pattern) (guard : d4203 p = 1) : d649 p ≤ (0 : Int) + d786 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d649, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2886 p hg
    simpa only [d649, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d649, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2902 p hg
    simpa only [d649, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2904 (p : Pattern) (guard : d4203 p = 1) : d650 p ≤ (0 : Int) + d787 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d650, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2810 p hg
    simpa only [d650, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d650, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2903 p hg
    simpa only [d650, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2905 (p : Pattern) (guard : d4203 p = 1) : d651 p ≤ (0 : Int) + d788 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d651, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2876 p hg
    simpa only [d651, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d651, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2904 p hg
    simpa only [d651, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2906 (p : Pattern) (guard : d4203 p = 1) : d652 p ≤ (0 : Int) + d789 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d652, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2863 p hg
    simpa only [d652, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d652, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2905 p hg
    simpa only [d652, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2907 (p : Pattern) (guard : d0 p = 1) : d29 p ≤ (0 : Int) + d4213 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2908 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2909 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2910 (p : Pattern) (guard : d4206 p = 1) : d33 p ≤ (0 : Int) + d15 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2908 p hg
    simpa only [d4206, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2909 p hg
    simpa only [d4206, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2911 (p : Pattern) (guard : d0 p = 1) : d36 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2912 (p : Pattern) (guard : d4206 p = 1) : d37 p ≤ (0 : Int) + d15 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2908 p hg
    simpa only [d4206, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2911 p hg
    simpa only [d4206, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2913 (p : Pattern) (guard : d4206 p = 1) : d38 p ≤ (0 : Int) + d15 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2910 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2912 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2914 (p : Pattern) (guard : d0 p = 1) : d41 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2915 (p : Pattern) (guard : d4206 p = 1) : d42 p ≤ (0 : Int) + d15 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2908 p hg
    simpa only [d4206, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2914 p hg
    simpa only [d4206, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2916 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2917 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d19 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2918 (p : Pattern) (guard : d4206 p = 1) : d43 p ≤ (0 : Int) + d19 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2916 p hg
    simpa only [d4206, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2917 p hg
    simpa only [d4206, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2919 (p : Pattern) (guard : d4206 p = 1) : d44 p ≤ (0 : Int) + d4209 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d44, d4209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2915 p hg
    simpa only [d44, d4209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d44, d4209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2918 p hg
    simpa only [d44, d4209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2920 (p : Pattern) (guard : d4206 p = 1) : d45 p ≤ (0 : Int) + d4210 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d45, d4210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2913 p hg
    simpa only [d45, d4210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d45, d4210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2919 p hg
    simpa only [d45, d4210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2921 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2922 (p : Pattern) (guard : d4206 p = 1) : d46 p ≤ (0 : Int) + d15 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2908 p hg
    simpa only [d4206, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2921 p hg
    simpa only [d4206, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2923 (p : Pattern) (guard : d4206 p = 1) : d47 p ≤ (0 : Int) + d4209 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d47, d4209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2922 p hg
    simpa only [d47, d4209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d47, d4209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2918 p hg
    simpa only [d47, d4209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2924 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (0 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2925 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d25 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2926 (p : Pattern) (guard : d4206 p = 1) : d48 p ≤ (0 : Int) + d25 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2924 p hg
    simpa only [d4206, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2925 p hg
    simpa only [d4206, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2927 (p : Pattern) (guard : d4206 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare2928 (p : Pattern) (guard : d4206 p = 1) : d49 p ≤ (0 : Int) + d4211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d49, d4211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2926 p hg
    simpa only [d49, d4211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d49, d4211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d49, d4211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2929 (p : Pattern) (guard : d4206 p = 1) : d50 p ≤ (0 : Int) + d4212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d50, d4212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2923 p hg
    simpa only [d50, d4212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d50, d4212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2928 p hg
    simpa only [d50, d4212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2930 (p : Pattern) (guard : d4206 p = 1) : d51 p ≤ (0 : Int) + d4213 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d51, d4213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2920 p hg
    simpa only [d51, d4213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d51, d4213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2929 p hg
    simpa only [d51, d4213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2931 (p : Pattern) (guard : d4207 p = 1) : d52 p ≤ (0 : Int) + d4213 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2907 p hg
    simpa only [d4207, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2930 p hg
    simpa only [d4207, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2932 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d4220 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2933 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2934 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d32 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2935 (p : Pattern) (guard : d4206 p = 1) : d66 p ≤ (0 : Int) + d32 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2933 p hg
    simpa only [d4206, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2934 p hg
    simpa only [d4206, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2936 (p : Pattern) (guard : d4206 p = 1) : d67 p ≤ (0 : Int) + d4214 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d67, d4214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2912 p hg
    simpa only [d67, d4214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d67, d4214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2935 p hg
    simpa only [d67, d4214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2937 (p : Pattern) (guard : d4206 p = 1) : d68 p ≤ (0 : Int) + d4215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d68, d4215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2918 p hg
    simpa only [d68, d4215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d68, d4215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2926 p hg
    simpa only [d68, d4215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2938 (p : Pattern) (guard : d4206 p = 1) : d69 p ≤ (0 : Int) + d4216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d69, d4216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2936 p hg
    simpa only [d69, d4216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d69, d4216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2937 p hg
    simpa only [d69, d4216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2939 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (0 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare815 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
