/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions22
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2760 (p : Pattern) : d543 (change p 138 (some 160)) = d4121 p := by
  change (if p 141 then d542 (change p 138 (some 160)) else d531 (change p 138 (some 160))) = d4121 p
  rw [sub2759, sub2747]
  rfl
theorem sub2761 (p : Pattern) : d544 (change p 138 (some 160)) = d4121 p := by
  change d543 (change p 138 (some 160)) = d4121 p
  exact sub2760 p
theorem sub2762 (p : Pattern) : d545 (change p 138 (some 160)) = d4122 p := by
  change (if p 116 then d544 (change p 138 (some 160)) else d517 (change p 138 (some 160))) = d4122 p
  rw [sub2761, sub2728]
  rfl
theorem sub2763 (p : Pattern) : d546 (change p 138 (some 160)) = d4120 p := by
  change d77 (change p 138 (some 160)) = d4120 p
  exact sub2727 p
theorem sub2764 (p : Pattern) : d547 (change p 138 (some 160)) = d4121 p := by
  change d543 (change p 138 (some 160)) = d4121 p
  exact sub2760 p
theorem sub2765 (p : Pattern) : d548 (change p 138 (some 160)) = d4122 p := by
  change (if p 116 then d547 (change p 138 (some 160)) else d546 (change p 138 (some 160))) = d4122 p
  rw [sub2764, sub2763]
  rfl
theorem sub2766 (p : Pattern) : d549 (change p 138 (some 160)) = d4122 p := by
  change (if p 115 then d548 (change p 138 (some 160)) else d545 (change p 138 (some 160))) = d4122 p
  rw [sub2765, sub2762]
  simp only [ite_self]
theorem sub2767 (p : Pattern) : d550 (change p 138 (some 160)) = d4120 p := by
  change d77 (change p 138 (some 160)) = d4120 p
  exact sub2727 p
theorem sub2768 (p : Pattern) : d551 (change p 138 (some 160)) = d4121 p := by
  change d543 (change p 138 (some 160)) = d4121 p
  exact sub2760 p
theorem sub2769 (p : Pattern) : d552 (change p 138 (some 160)) = d4122 p := by
  change (if p 116 then d551 (change p 138 (some 160)) else d550 (change p 138 (some 160))) = d4122 p
  rw [sub2768, sub2767]
  rfl
theorem sub2770 (p : Pattern) : d553 (change p 138 (some 160)) = d4120 p := by
  change d77 (change p 138 (some 160)) = d4120 p
  exact sub2727 p
theorem sub2771 (p : Pattern) : d554 (change p 138 (some 160)) = d4122 p := by
  change (if p 116 then d547 (change p 138 (some 160)) else d553 (change p 138 (some 160))) = d4122 p
  rw [sub2764, sub2770]
  rfl
theorem sub2772 (p : Pattern) : d555 (change p 138 (some 160)) = d4122 p := by
  change (if p 115 then d554 (change p 138 (some 160)) else d552 (change p 138 (some 160))) = d4122 p
  rw [sub2771, sub2769]
  simp only [ite_self]
theorem sub2773 (p : Pattern) : d556 (change p 138 (some 160)) = d4122 p := by
  change (if p 71 then d555 (change p 138 (some 160)) else d549 (change p 138 (some 160))) = d4122 p
  rw [sub2772, sub2766]
  simp only [ite_self]
theorem sub2774 (p : Pattern) : d1 (change p 138 (some 160)) = d1 p := by
  rfl
theorem sub2775 (p : Pattern) : d102 (change p 138 (some 160)) = d102 p := by
  change (if p 247 then d12 (change p 138 (some 160)) else d1 (change p 138 (some 160))) = d102 p
  rw [sub2678, sub2774]
  rfl
theorem sub2776 (p : Pattern) : d103 (change p 138 (some 160)) = d103 p := by
  change (if p 246 then d102 (change p 138 (some 160)) else d1 (change p 138 (some 160))) = d103 p
  rw [sub2775, sub2774]
  rfl
theorem sub2777 (p : Pattern) : d3 (change p 138 (some 160)) = d3 p := by
  rfl
theorem sub2778 (p : Pattern) : d115 (change p 138 (some 160)) = d115 p := by
  change (if p 247 then d12 (change p 138 (some 160)) else d3 (change p 138 (some 160))) = d115 p
  rw [sub2678, sub2777]
  rfl
theorem sub2779 (p : Pattern) : d116 (change p 138 (some 160)) = d116 p := by
  change (if p 246 then d115 (change p 138 (some 160)) else d3 (change p 138 (some 160))) = d116 p
  rw [sub2778, sub2777]
  rfl
theorem sub2780 (p : Pattern) : d117 (change p 138 (some 160)) = d117 p := by
  change (if p 204 then d12 (change p 138 (some 160)) else d116 (change p 138 (some 160))) = d117 p
  rw [sub2678, sub2779]
  rfl
theorem sub2781 (p : Pattern) : d118 (change p 138 (some 160)) = d118 p := by
  change (if p 182 then d117 (change p 138 (some 160)) else d103 (change p 138 (some 160))) = d118 p
  rw [sub2780, sub2776]
  rfl
theorem sub2782 (p : Pattern) : d7 (change p 138 (some 160)) = d7 p := by
  rfl
theorem sub2783 (p : Pattern) : d119 (change p 138 (some 160)) = d119 p := by
  change (if p 247 then d12 (change p 138 (some 160)) else d7 (change p 138 (some 160))) = d119 p
  rw [sub2678, sub2782]
  rfl
theorem sub2784 (p : Pattern) : d120 (change p 138 (some 160)) = d120 p := by
  change (if p 246 then d119 (change p 138 (some 160)) else d7 (change p 138 (some 160))) = d120 p
  rw [sub2783, sub2782]
  rfl
theorem sub2785 (p : Pattern) : d121 (change p 138 (some 160)) = d121 p := by
  change (if p 204 then d12 (change p 138 (some 160)) else d120 (change p 138 (some 160))) = d121 p
  rw [sub2678, sub2784]
  rfl
theorem sub2786 (p : Pattern) : d122 (change p 138 (some 160)) = d122 p := by
  change (if p 182 then d121 (change p 138 (some 160)) else d103 (change p 138 (some 160))) = d122 p
  rw [sub2785, sub2776]
  rfl
theorem sub2787 (p : Pattern) : d123 (change p 138 (some 160)) = d123 p := by
  change (if p 163 then d122 (change p 138 (some 160)) else d118 (change p 138 (some 160))) = d123 p
  rw [sub2786, sub2781]
  rfl
theorem sub2788 (p : Pattern) : d124 (change p 138 (some 160)) = d124 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d103 (change p 138 (some 160))) = d124 p
  rw [sub2678, sub2776]
  rfl
theorem sub2789 (p : Pattern) : d5 (change p 138 (some 160)) = d5 p := by
  rfl
theorem sub2790 (p : Pattern) : d106 (change p 138 (some 160)) = d106 p := by
  change (if p 247 then d12 (change p 138 (some 160)) else d5 (change p 138 (some 160))) = d106 p
  rw [sub2678, sub2789]
  rfl
theorem sub2791 (p : Pattern) : d107 (change p 138 (some 160)) = d107 p := by
  change (if p 246 then d106 (change p 138 (some 160)) else d5 (change p 138 (some 160))) = d107 p
  rw [sub2790, sub2789]
  rfl
theorem sub2792 (p : Pattern) : d125 (change p 138 (some 160)) = d125 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d107 (change p 138 (some 160))) = d125 p
  rw [sub2678, sub2791]
  rfl
theorem sub2793 (p : Pattern) : d126 (change p 138 (some 160)) = d126 p := by
  change (if p 163 then d125 (change p 138 (some 160)) else d124 (change p 138 (some 160))) = d126 p
  rw [sub2792, sub2788]
  rfl
theorem sub2794 (p : Pattern) : d127 (change p 138 (some 160)) = d127 p := by
  change (if p 162 then d126 (change p 138 (some 160)) else d123 (change p 138 (some 160))) = d127 p
  rw [sub2793, sub2787]
  rfl
theorem sub2795 (p : Pattern) : d128 (change p 138 (some 160)) = d128 p := by
  change (if p 163 then d12 (change p 138 (some 160)) else d70 (change p 138 (some 160))) = d128 p
  rw [sub2678, sub2720]
  rfl
theorem sub2796 (p : Pattern) : d129 (change p 138 (some 160)) = d129 p := by
  change (if p 162 then d128 (change p 138 (some 160)) else d126 (change p 138 (some 160))) = d129 p
  rw [sub2795, sub2793]
  rfl
theorem sub2797 (p : Pattern) : d130 (change p 138 (some 160)) = d130 p := by
  change (if p 161 then d129 (change p 138 (some 160)) else d127 (change p 138 (some 160))) = d130 p
  rw [sub2796, sub2794]
  rfl
theorem sub2798 (p : Pattern) : d131 (change p 138 (some 160)) = d130 p := by
  change d130 (change p 138 (some 160)) = d130 p
  exact sub2797 p
theorem sub2799 (p : Pattern) : d139 (change p 138 (some 160)) = d139 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d116 (change p 138 (some 160))) = d139 p
  rw [sub2678, sub2779]
  rfl
theorem sub2800 (p : Pattern) : d140 (change p 138 (some 160)) = d140 p := by
  change (if p 163 then d139 (change p 138 (some 160)) else d122 (change p 138 (some 160))) = d140 p
  rw [sub2799, sub2786]
  rfl
theorem sub2801 (p : Pattern) : d141 (change p 138 (some 160)) = d141 p := by
  change (if p 163 then d70 (change p 138 (some 160)) else d125 (change p 138 (some 160))) = d141 p
  rw [sub2720, sub2792]
  rfl
theorem sub2802 (p : Pattern) : d142 (change p 138 (some 160)) = d142 p := by
  change (if p 162 then d141 (change p 138 (some 160)) else d140 (change p 138 (some 160))) = d142 p
  rw [sub2801, sub2800]
  rfl
theorem sub2803 (p : Pattern) : d143 (change p 138 (some 160)) = d143 p := by
  change (if p 163 then d72 (change p 138 (some 160)) else d125 (change p 138 (some 160))) = d143 p
  rw [sub2722, sub2792]
  rfl
theorem sub2804 (p : Pattern) : d144 (change p 138 (some 160)) = d144 p := by
  change (if p 162 then d12 (change p 138 (some 160)) else d143 (change p 138 (some 160))) = d144 p
  rw [sub2678, sub2803]
  rfl
theorem sub2805 (p : Pattern) : d145 (change p 138 (some 160)) = d145 p := by
  change (if p 161 then d144 (change p 138 (some 160)) else d142 (change p 138 (some 160))) = d145 p
  rw [sub2804, sub2802]
  rfl
theorem sub2806 (p : Pattern) : d146 (change p 138 (some 160)) = d145 p := by
  change d145 (change p 138 (some 160)) = d145 p
  exact sub2805 p
theorem sub2807 (p : Pattern) : d147 (change p 138 (some 160)) = d4123 p := by
  change (if p 141 then d146 (change p 138 (some 160)) else d131 (change p 138 (some 160))) = d4123 p
  rw [sub2806, sub2798]
  rfl
theorem sub2808 (p : Pattern) : d557 (change p 138 (some 160)) = d4123 p := by
  change d147 (change p 138 (some 160)) = d4123 p
  exact sub2807 p
theorem sub2809 (p : Pattern) : d558 (change p 138 (some 160)) = d558 p := by
  change (if p 204 then d107 (change p 138 (some 160)) else d103 (change p 138 (some 160))) = d558 p
  rw [sub2791, sub2776]
  rfl
theorem sub2810 (p : Pattern) : d559 (change p 138 (some 160)) = d559 p := by
  change (if p 182 then d121 (change p 138 (some 160)) else d558 (change p 138 (some 160))) = d559 p
  rw [sub2785, sub2809]
  rfl
theorem sub2811 (p : Pattern) : d560 (change p 138 (some 160)) = d560 p := by
  change (if p 182 then d41 (change p 138 (some 160)) else d558 (change p 138 (some 160))) = d560 p
  rw [sub2695, sub2809]
  rfl
theorem sub2812 (p : Pattern) : d561 (change p 138 (some 160)) = d561 p := by
  change (if p 163 then d560 (change p 138 (some 160)) else d559 (change p 138 (some 160))) = d561 p
  rw [sub2811, sub2810]
  rfl
theorem sub2813 (p : Pattern) : d562 (change p 138 (some 160)) = d562 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d558 (change p 138 (some 160))) = d562 p
  rw [sub2678, sub2809]
  rfl
theorem sub2814 (p : Pattern) : d563 (change p 138 (some 160)) = d563 p := by
  change (if p 204 then d24 (change p 138 (some 160)) else d107 (change p 138 (some 160))) = d563 p
  rw [sub2707, sub2791]
  rfl
theorem sub2815 (p : Pattern) : d564 (change p 138 (some 160)) = d564 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d563 (change p 138 (some 160))) = d564 p
  rw [sub2678, sub2814]
  rfl
theorem sub2816 (p : Pattern) : d565 (change p 138 (some 160)) = d565 p := by
  change (if p 163 then d564 (change p 138 (some 160)) else d562 (change p 138 (some 160))) = d565 p
  rw [sub2815, sub2813]
  rfl
theorem sub2817 (p : Pattern) : d566 (change p 138 (some 160)) = d566 p := by
  change (if p 162 then d565 (change p 138 (some 160)) else d561 (change p 138 (some 160))) = d566 p
  rw [sub2816, sub2812]
  rfl
theorem sub2818 (p : Pattern) : d278 (change p 138 (some 160)) = d278 p := by
  change (if p 163 then d12 (change p 138 (some 160)) else d277 (change p 138 (some 160))) = d278 p
  rw [sub2678, sub2753]
  rfl
theorem sub2819 (p : Pattern) : d567 (change p 138 (some 160)) = d567 p := by
  change (if p 162 then d278 (change p 138 (some 160)) else d565 (change p 138 (some 160))) = d567 p
  rw [sub2818, sub2816]
  rfl
theorem sub2820 (p : Pattern) : d568 (change p 138 (some 160)) = d568 p := by
  change (if p 161 then d567 (change p 138 (some 160)) else d566 (change p 138 (some 160))) = d568 p
  rw [sub2819, sub2817]
  rfl
theorem sub2821 (p : Pattern) : d569 (change p 138 (some 160)) = d568 p := by
  change d568 (change p 138 (some 160)) = d568 p
  exact sub2820 p
theorem sub2822 (p : Pattern) : d570 (change p 138 (some 160)) = d570 p := by
  change (if p 204 then d120 (change p 138 (some 160)) else d116 (change p 138 (some 160))) = d570 p
  rw [sub2784, sub2779]
  rfl
theorem sub2823 (p : Pattern) : d571 (change p 138 (some 160)) = d571 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d570 (change p 138 (some 160))) = d571 p
  rw [sub2678, sub2822]
  rfl
theorem sub2824 (p : Pattern) : d572 (change p 138 (some 160)) = d572 p := by
  change (if p 163 then d571 (change p 138 (some 160)) else d560 (change p 138 (some 160))) = d572 p
  rw [sub2823, sub2811]
  rfl
theorem sub2825 (p : Pattern) : d573 (change p 138 (some 160)) = d573 p := by
  change (if p 163 then d277 (change p 138 (some 160)) else d564 (change p 138 (some 160))) = d573 p
  rw [sub2753, sub2815]
  rfl
theorem sub2826 (p : Pattern) : d574 (change p 138 (some 160)) = d574 p := by
  change (if p 162 then d573 (change p 138 (some 160)) else d572 (change p 138 (some 160))) = d574 p
  rw [sub2825, sub2824]
  rfl
theorem sub2827 (p : Pattern) : d575 (change p 138 (some 160)) = d575 p := by
  change (if p 163 then d538 (change p 138 (some 160)) else d564 (change p 138 (some 160))) = d575 p
  rw [sub2755, sub2815]
  rfl
theorem sub2828 (p : Pattern) : d576 (change p 138 (some 160)) = d576 p := by
  change (if p 162 then d12 (change p 138 (some 160)) else d575 (change p 138 (some 160))) = d576 p
  rw [sub2678, sub2827]
  rfl
theorem sub2829 (p : Pattern) : d577 (change p 138 (some 160)) = d577 p := by
  change (if p 161 then d576 (change p 138 (some 160)) else d574 (change p 138 (some 160))) = d577 p
  rw [sub2828, sub2826]
  rfl
theorem sub2830 (p : Pattern) : d578 (change p 138 (some 160)) = d577 p := by
  change d577 (change p 138 (some 160)) = d577 p
  exact sub2829 p
theorem sub2831 (p : Pattern) : d579 (change p 138 (some 160)) = d4124 p := by
  change (if p 141 then d578 (change p 138 (some 160)) else d569 (change p 138 (some 160))) = d4124 p
  rw [sub2830, sub2821]
  rfl
theorem sub2832 (p : Pattern) : d580 (change p 138 (some 160)) = d4124 p := by
  change d579 (change p 138 (some 160)) = d4124 p
  exact sub2831 p
theorem sub2833 (p : Pattern) : d581 (change p 138 (some 160)) = d4125 p := by
  change (if p 116 then d580 (change p 138 (some 160)) else d557 (change p 138 (some 160))) = d4125 p
  rw [sub2832, sub2808]
  rfl
theorem sub2834 (p : Pattern) : d582 (change p 138 (some 160)) = d4123 p := by
  change d147 (change p 138 (some 160)) = d4123 p
  exact sub2807 p
theorem sub2835 (p : Pattern) : d583 (change p 138 (some 160)) = d4124 p := by
  change d579 (change p 138 (some 160)) = d4124 p
  exact sub2831 p
theorem sub2836 (p : Pattern) : d584 (change p 138 (some 160)) = d4125 p := by
  change (if p 116 then d583 (change p 138 (some 160)) else d582 (change p 138 (some 160))) = d4125 p
  rw [sub2835, sub2834]
  rfl
theorem sub2837 (p : Pattern) : d585 (change p 138 (some 160)) = d4125 p := by
  change (if p 115 then d584 (change p 138 (some 160)) else d581 (change p 138 (some 160))) = d4125 p
  rw [sub2836, sub2833]
  simp only [ite_self]
theorem sub2838 (p : Pattern) : d586 (change p 138 (some 160)) = d4126 p := by
  change (if p 71 then d585 (change p 138 (some 160)) else d549 (change p 138 (some 160))) = d4126 p
  rw [sub2837, sub2766]
  rfl
theorem sub2839 (p : Pattern) : d587 (change p 138 (some 160)) = d4127 p := by
  change (if p 49 then d586 (change p 138 (some 160)) else d556 (change p 138 (some 160))) = d4127 p
  rw [sub2838, sub2773]
  rfl
theorem sub2840 (p : Pattern) : d588 (change p 138 (some 160)) = d588 p := by
  change (if p 204 then d18 (change p 138 (some 160)) else d31 (change p 138 (some 160))) = d588 p
  rw [sub2699, sub2683]
  rfl
theorem sub2841 (p : Pattern) : d589 (change p 138 (some 160)) = d589 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d588 (change p 138 (some 160))) = d589 p
  rw [sub2678, sub2840]
  rfl
theorem sub2842 (p : Pattern) : d590 (change p 138 (some 160)) = d590 p := by
  change (if p 204 then d191 (change p 138 (some 160)) else d35 (change p 138 (some 160))) = d590 p
  rw [sub2737, sub2688]
  rfl
theorem sub2843 (p : Pattern) : d591 (change p 138 (some 160)) = d591 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d590 (change p 138 (some 160))) = d591 p
  rw [sub2678, sub2842]
  rfl
theorem sub2844 (p : Pattern) : d592 (change p 138 (some 160)) = d592 p := by
  change (if p 163 then d591 (change p 138 (some 160)) else d589 (change p 138 (some 160))) = d592 p
  rw [sub2843, sub2841]
  rfl
theorem sub2845 (p : Pattern) : d593 (change p 138 (some 160)) = d593 p := by
  change (if p 162 then d592 (change p 138 (some 160)) else d521 (change p 138 (some 160))) = d593 p
  rw [sub2844, sub2733]
  rfl
theorem sub2846 (p : Pattern) : d594 (change p 138 (some 160)) = d594 p := by
  change (if p 162 then d539 (change p 138 (some 160)) else d592 (change p 138 (some 160))) = d594 p
  rw [sub2756, sub2844]
  rfl
theorem sub2847 (p : Pattern) : d595 (change p 138 (some 160)) = d595 p := by
  change (if p 161 then d594 (change p 138 (some 160)) else d593 (change p 138 (some 160))) = d595 p
  rw [sub2846, sub2845]
  rfl
theorem sub2848 (p : Pattern) : d596 (change p 138 (some 160)) = d595 p := by
  change d595 (change p 138 (some 160)) = d595 p
  exact sub2847 p
theorem sub2849 (p : Pattern) : d597 (change p 138 (some 160)) = d597 p := by
  change (if p 182 then d59 (change p 138 (some 160)) else d588 (change p 138 (some 160))) = d597 p
  rw [sub2731, sub2840]
  rfl
theorem sub2850 (p : Pattern) : d598 (change p 138 (some 160)) = d598 p := by
  change (if p 163 then d533 (change p 138 (some 160)) else d597 (change p 138 (some 160))) = d598 p
  rw [sub2749, sub2849]
  rfl
theorem sub2851 (p : Pattern) : d599 (change p 138 (some 160)) = d599 p := by
  change (if p 163 then d538 (change p 138 (some 160)) else d524 (change p 138 (some 160))) = d599 p
  rw [sub2755, sub2739]
  rfl
theorem sub2852 (p : Pattern) : d600 (change p 138 (some 160)) = d600 p := by
  change (if p 162 then d599 (change p 138 (some 160)) else d598 (change p 138 (some 160))) = d600 p
  rw [sub2851, sub2850]
  rfl
theorem sub2853 (p : Pattern) : d601 (change p 138 (some 160)) = d601 p := by
  change (if p 163 then d12 (change p 138 (some 160)) else d591 (change p 138 (some 160))) = d601 p
  rw [sub2678, sub2843]
  rfl
theorem sub2854 (p : Pattern) : d602 (change p 138 (some 160)) = d602 p := by
  change (if p 162 then d12 (change p 138 (some 160)) else d601 (change p 138 (some 160))) = d602 p
  rw [sub2678, sub2853]
  rfl
theorem sub2855 (p : Pattern) : d603 (change p 138 (some 160)) = d603 p := by
  change (if p 161 then d602 (change p 138 (some 160)) else d600 (change p 138 (some 160))) = d603 p
  rw [sub2854, sub2852]
  rfl
theorem sub2856 (p : Pattern) : d604 (change p 138 (some 160)) = d603 p := by
  change d603 (change p 138 (some 160)) = d603 p
  exact sub2855 p
theorem sub2857 (p : Pattern) : d605 (change p 138 (some 160)) = d4128 p := by
  change (if p 141 then d604 (change p 138 (some 160)) else d596 (change p 138 (some 160))) = d4128 p
  rw [sub2856, sub2848]
  rfl
theorem sub2858 (p : Pattern) : d606 (change p 138 (some 160)) = d4128 p := by
  change d605 (change p 138 (some 160)) = d4128 p
  exact sub2857 p
theorem sub2859 (p : Pattern) : d607 (change p 138 (some 160)) = d4129 p := by
  change (if p 116 then d606 (change p 138 (some 160)) else d553 (change p 138 (some 160))) = d4129 p
  rw [sub2858, sub2770]
  rfl
theorem sub2860 (p : Pattern) : d608 (change p 138 (some 160)) = d4130 p := by
  change (if p 115 then d607 (change p 138 (some 160)) else d552 (change p 138 (some 160))) = d4130 p
  rw [sub2859, sub2769]
  rfl
theorem sub2861 (p : Pattern) : d609 (change p 138 (some 160)) = d4131 p := by
  change (if p 71 then d608 (change p 138 (some 160)) else d549 (change p 138 (some 160))) = d4131 p
  rw [sub2860, sub2766]
  rfl
theorem sub2862 (p : Pattern) : d215 (change p 138 (some 160)) = d215 p := by
  change (if p 163 then d12 (change p 138 (some 160)) else d125 (change p 138 (some 160))) = d215 p
  rw [sub2678, sub2792]
  rfl
theorem sub2863 (p : Pattern) : d216 (change p 138 (some 160)) = d216 p := by
  change (if p 162 then d215 (change p 138 (some 160)) else d140 (change p 138 (some 160))) = d216 p
  rw [sub2862, sub2800]
  rfl
theorem sub2864 (p : Pattern) : d217 (change p 138 (some 160)) = d217 p := by
  change (if p 162 then d12 (change p 138 (some 160)) else d215 (change p 138 (some 160))) = d217 p
  rw [sub2678, sub2862]
  rfl
theorem sub2865 (p : Pattern) : d218 (change p 138 (some 160)) = d218 p := by
  change (if p 161 then d217 (change p 138 (some 160)) else d216 (change p 138 (some 160))) = d218 p
  rw [sub2864, sub2863]
  rfl
theorem sub2866 (p : Pattern) : d219 (change p 138 (some 160)) = d218 p := by
  change d218 (change p 138 (some 160)) = d218 p
  exact sub2865 p
theorem sub2867 (p : Pattern) : d220 (change p 138 (some 160)) = d4132 p := by
  change (if p 141 then d219 (change p 138 (some 160)) else d131 (change p 138 (some 160))) = d4132 p
  rw [sub2866, sub2798]
  rfl
theorem sub2868 (p : Pattern) : d610 (change p 138 (some 160)) = d4132 p := by
  change d220 (change p 138 (some 160)) = d4132 p
  exact sub2867 p
theorem sub2869 (p : Pattern) : d611 (change p 138 (some 160)) = d611 p := by
  change (if p 163 then d12 (change p 138 (some 160)) else d564 (change p 138 (some 160))) = d611 p
  rw [sub2678, sub2815]
  rfl
theorem sub2870 (p : Pattern) : d612 (change p 138 (some 160)) = d612 p := by
  change (if p 162 then d611 (change p 138 (some 160)) else d572 (change p 138 (some 160))) = d612 p
  rw [sub2869, sub2824]
  rfl
theorem sub2871 (p : Pattern) : d613 (change p 138 (some 160)) = d613 p := by
  change (if p 162 then d12 (change p 138 (some 160)) else d611 (change p 138 (some 160))) = d613 p
  rw [sub2678, sub2869]
  rfl
theorem sub2872 (p : Pattern) : d614 (change p 138 (some 160)) = d614 p := by
  change (if p 161 then d613 (change p 138 (some 160)) else d612 (change p 138 (some 160))) = d614 p
  rw [sub2871, sub2870]
  rfl
theorem sub2873 (p : Pattern) : d615 (change p 138 (some 160)) = d614 p := by
  change d614 (change p 138 (some 160)) = d614 p
  exact sub2872 p
theorem sub2874 (p : Pattern) : d616 (change p 138 (some 160)) = d4133 p := by
  change (if p 141 then d615 (change p 138 (some 160)) else d569 (change p 138 (some 160))) = d4133 p
  rw [sub2873, sub2821]
  rfl
theorem sub2875 (p : Pattern) : d617 (change p 138 (some 160)) = d4133 p := by
  change d616 (change p 138 (some 160)) = d4133 p
  exact sub2874 p
theorem sub2876 (p : Pattern) : d618 (change p 138 (some 160)) = d4134 p := by
  change (if p 116 then d617 (change p 138 (some 160)) else d610 (change p 138 (some 160))) = d4134 p
  rw [sub2875, sub2868]
  rfl
theorem sub2877 (p : Pattern) : d268 (change p 138 (some 160)) = d268 p := by
  change (if p 204 then d116 (change p 138 (some 160)) else d103 (change p 138 (some 160))) = d268 p
  rw [sub2779, sub2776]
  rfl
theorem sub2878 (p : Pattern) : d269 (change p 138 (some 160)) = d269 p := by
  change (if p 182 then d117 (change p 138 (some 160)) else d268 (change p 138 (some 160))) = d269 p
  rw [sub2780, sub2877]
  rfl
theorem sub2879 (p : Pattern) : d270 (change p 138 (some 160)) = d270 p := by
  change (if p 182 then d121 (change p 138 (some 160)) else d268 (change p 138 (some 160))) = d270 p
  rw [sub2785, sub2877]
  rfl
end NetHack.Sokoban22Refined85
