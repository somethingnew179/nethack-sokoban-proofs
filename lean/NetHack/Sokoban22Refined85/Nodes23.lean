/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes22
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d2760 (p : Pattern) : Int := if p 163 then d2753 p else d2746 p
theorem agree2760 (p q : Pattern) (h : Agree support p q) : d2760 p = d2760 q := by
  simp only [d2760, h 163 (by decide), agree2753 p q h, agree2746 p q h]
theorem nonnegative2760 (p : Pattern) : 0 ≤ d2760 p :=
  nonnegative_ite (p 163) (nonnegative2753 p) (nonnegative2746 p)
def d2761 (p : Pattern) : Int := if p 163 then d2581 p else d2748 p
theorem agree2761 (p q : Pattern) (h : Agree support p q) : d2761 p = d2761 q := by
  simp only [d2761, h 163 (by decide), agree2581 p q h, agree2748 p q h]
theorem nonnegative2761 (p : Pattern) : 0 ≤ d2761 p :=
  nonnegative_ite (p 163) (nonnegative2581 p) (nonnegative2748 p)
def d2762 (p : Pattern) : Int := if p 162 then d2761 p else d2760 p
theorem agree2762 (p q : Pattern) (h : Agree support p q) : d2762 p = d2762 q := by
  simp only [d2762, h 162 (by decide), agree2761 p q h, agree2760 p q h]
theorem nonnegative2762 (p : Pattern) : 0 ≤ d2762 p :=
  nonnegative_ite (p 162) (nonnegative2761 p) (nonnegative2760 p)
def d2763 (p : Pattern) : Int := if p 163 then d2584 p else d2748 p
theorem agree2763 (p q : Pattern) (h : Agree support p q) : d2763 p = d2763 q := by
  simp only [d2763, h 163 (by decide), agree2584 p q h, agree2748 p q h]
theorem nonnegative2763 (p : Pattern) : 0 ≤ d2763 p :=
  nonnegative_ite (p 163) (nonnegative2584 p) (nonnegative2748 p)
def d2764 (p : Pattern) : Int := if p 162 then d12 p else d2763 p
theorem agree2764 (p q : Pattern) (h : Agree support p q) : d2764 p = d2764 q := by
  simp only [d2764, h 162 (by decide), agree12 p q h, agree2763 p q h]
theorem nonnegative2764 (p : Pattern) : 0 ≤ d2764 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2763 p)
def d2765 (p : Pattern) : Int := if p 161 then d2764 p else d2762 p
theorem agree2765 (p q : Pattern) (h : Agree support p q) : d2765 p = d2765 q := by
  simp only [d2765, h 161 (by decide), agree2764 p q h, agree2762 p q h]
theorem nonnegative2765 (p : Pattern) : 0 ≤ d2765 p :=
  nonnegative_ite (p 161) (nonnegative2764 p) (nonnegative2762 p)
def d2766 (p : Pattern) : Int := if p 163 then d12 p else d2755 p
theorem agree2766 (p q : Pattern) (h : Agree support p q) : d2766 p = d2766 q := by
  simp only [d2766, h 163 (by decide), agree12 p q h, agree2755 p q h]
theorem nonnegative2766 (p : Pattern) : 0 ≤ d2766 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2755 p)
def d2767 (p : Pattern) : Int := if p 162 then d12 p else d2766 p
theorem agree2767 (p q : Pattern) (h : Agree support p q) : d2767 p = d2767 q := by
  simp only [d2767, h 162 (by decide), agree12 p q h, agree2766 p q h]
theorem nonnegative2767 (p : Pattern) : 0 ≤ d2767 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2766 p)
def d2768 (p : Pattern) : Int := if p 161 then d12 p else d2767 p
theorem agree2768 (p q : Pattern) (h : Agree support p q) : d2768 p = d2768 q := by
  simp only [d2768, h 161 (by decide), agree12 p q h, agree2767 p q h]
theorem nonnegative2768 (p : Pattern) : 0 ≤ d2768 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2767 p)
def d2769 (p : Pattern) : Int := if p 160 then d2768 p else d2765 p
theorem agree2769 (p q : Pattern) (h : Agree support p q) : d2769 p = d2769 q := by
  simp only [d2769, h 160 (by decide), agree2768 p q h, agree2765 p q h]
theorem nonnegative2769 (p : Pattern) : 0 ≤ d2769 p :=
  nonnegative_ite (p 160) (nonnegative2768 p) (nonnegative2765 p)
def d2770 (p : Pattern) : Int := if p 141 then d2769 p else d2759 p
theorem agree2770 (p q : Pattern) (h : Agree support p q) : d2770 p = d2770 q := by
  simp only [d2770, h 141 (by decide), agree2769 p q h, agree2759 p q h]
theorem nonnegative2770 (p : Pattern) : 0 ≤ d2770 p :=
  nonnegative_ite (p 141) (nonnegative2769 p) (nonnegative2759 p)
def d2771 (p : Pattern) : Int := if p 138 then d2770 p else d2744 p
theorem agree2771 (p q : Pattern) (h : Agree support p q) : d2771 p = d2771 q := by
  simp only [d2771, h 138 (by decide), agree2770 p q h, agree2744 p q h]
theorem nonnegative2771 (p : Pattern) : 0 ≤ d2771 p :=
  nonnegative_ite (p 138) (nonnegative2770 p) (nonnegative2744 p)
def d2772 (p : Pattern) : Int := if p 162 then d12 p else d2699 p
theorem agree2772 (p q : Pattern) (h : Agree support p q) : d2772 p = d2772 q := by
  simp only [d2772, h 162 (by decide), agree12 p q h, agree2699 p q h]
theorem nonnegative2772 (p : Pattern) : 0 ≤ d2772 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2699 p)
def d2773 (p : Pattern) : Int := if p 161 then d12 p else d2772 p
theorem agree2773 (p q : Pattern) (h : Agree support p q) : d2773 p = d2773 q := by
  simp only [d2773, h 161 (by decide), agree12 p q h, agree2772 p q h]
theorem nonnegative2773 (p : Pattern) : 0 ≤ d2773 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2772 p)
def d2774 (p : Pattern) : Int := if p 160 then d12 p else d2773 p
theorem agree2774 (p q : Pattern) (h : Agree support p q) : d2774 p = d2774 q := by
  simp only [d2774, h 160 (by decide), agree12 p q h, agree2773 p q h]
theorem nonnegative2774 (p : Pattern) : 0 ≤ d2774 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative2773 p)
def d2775 (p : Pattern) : Int := if p 141 then d12 p else d2774 p
theorem agree2775 (p q : Pattern) (h : Agree support p q) : d2775 p = d2775 q := by
  simp only [d2775, h 141 (by decide), agree12 p q h, agree2774 p q h]
theorem nonnegative2775 (p : Pattern) : 0 ≤ d2775 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative2774 p)
def d2776 (p : Pattern) : Int := if p 138 then d2775 p else d2770 p
theorem agree2776 (p q : Pattern) (h : Agree support p q) : d2776 p = d2776 q := by
  simp only [d2776, h 138 (by decide), agree2775 p q h, agree2770 p q h]
theorem nonnegative2776 (p : Pattern) : 0 ≤ d2776 p :=
  nonnegative_ite (p 138) (nonnegative2775 p) (nonnegative2770 p)
def d2777 (p : Pattern) : Int := if p 116 then d2776 p else d2771 p
theorem agree2777 (p q : Pattern) (h : Agree support p q) : d2777 p = d2777 q := by
  simp only [d2777, h 116 (by decide), agree2776 p q h, agree2771 p q h]
theorem nonnegative2777 (p : Pattern) : 0 ≤ d2777 p :=
  nonnegative_ite (p 116) (nonnegative2776 p) (nonnegative2771 p)
def d2778 (p : Pattern) : Int := if p 162 then d2697 p else d2687 p
theorem agree2778 (p q : Pattern) (h : Agree support p q) : d2778 p = d2778 q := by
  simp only [d2778, h 162 (by decide), agree2697 p q h, agree2687 p q h]
theorem nonnegative2778 (p : Pattern) : 0 ≤ d2778 p :=
  nonnegative_ite (p 162) (nonnegative2697 p) (nonnegative2687 p)
def d2779 (p : Pattern) : Int := if p 161 then d2700 p else d2778 p
theorem agree2779 (p q : Pattern) (h : Agree support p q) : d2779 p = d2779 q := by
  simp only [d2779, h 161 (by decide), agree2700 p q h, agree2778 p q h]
theorem nonnegative2779 (p : Pattern) : 0 ≤ d2779 p :=
  nonnegative_ite (p 161) (nonnegative2700 p) (nonnegative2778 p)
def d2780 (p : Pattern) : Int := if p 160 then d2719 p else d2779 p
theorem agree2780 (p q : Pattern) (h : Agree support p q) : d2780 p = d2780 q := by
  simp only [d2780, h 160 (by decide), agree2719 p q h, agree2779 p q h]
theorem nonnegative2780 (p : Pattern) : 0 ≤ d2780 p :=
  nonnegative_ite (p 160) (nonnegative2719 p) (nonnegative2779 p)
def d2781 (p : Pattern) : Int := if p 163 then d2729 p else d2687 p
theorem agree2781 (p q : Pattern) (h : Agree support p q) : d2781 p = d2781 q := by
  simp only [d2781, h 163 (by decide), agree2729 p q h, agree2687 p q h]
theorem nonnegative2781 (p : Pattern) : 0 ≤ d2781 p :=
  nonnegative_ite (p 163) (nonnegative2729 p) (nonnegative2687 p)
def d2782 (p : Pattern) : Int := if p 162 then d2731 p else d2781 p
theorem agree2782 (p q : Pattern) (h : Agree support p q) : d2782 p = d2782 q := by
  simp only [d2782, h 162 (by decide), agree2731 p q h, agree2781 p q h]
theorem nonnegative2782 (p : Pattern) : 0 ≤ d2782 p :=
  nonnegative_ite (p 162) (nonnegative2731 p) (nonnegative2781 p)
def d2783 (p : Pattern) : Int := if p 161 then d2734 p else d2782 p
theorem agree2783 (p q : Pattern) (h : Agree support p q) : d2783 p = d2783 q := by
  simp only [d2783, h 161 (by decide), agree2734 p q h, agree2782 p q h]
theorem nonnegative2783 (p : Pattern) : 0 ≤ d2783 p :=
  nonnegative_ite (p 161) (nonnegative2734 p) (nonnegative2782 p)
def d2784 (p : Pattern) : Int := if p 160 then d2742 p else d2783 p
theorem agree2784 (p q : Pattern) (h : Agree support p q) : d2784 p = d2784 q := by
  simp only [d2784, h 160 (by decide), agree2742 p q h, agree2783 p q h]
theorem nonnegative2784 (p : Pattern) : 0 ≤ d2784 p :=
  nonnegative_ite (p 160) (nonnegative2742 p) (nonnegative2783 p)
def d2785 (p : Pattern) : Int := if p 141 then d2784 p else d2780 p
theorem agree2785 (p q : Pattern) (h : Agree support p q) : d2785 p = d2785 q := by
  simp only [d2785, h 141 (by decide), agree2784 p q h, agree2780 p q h]
theorem nonnegative2785 (p : Pattern) : 0 ≤ d2785 p :=
  nonnegative_ite (p 141) (nonnegative2784 p) (nonnegative2780 p)
def d2786 (p : Pattern) : Int := if p 138 then d2770 p else d2785 p
theorem agree2786 (p q : Pattern) (h : Agree support p q) : d2786 p = d2786 q := by
  simp only [d2786, h 138 (by decide), agree2770 p q h, agree2785 p q h]
theorem nonnegative2786 (p : Pattern) : 0 ≤ d2786 p :=
  nonnegative_ite (p 138) (nonnegative2770 p) (nonnegative2785 p)
def d2787 (p : Pattern) : Int := if p 138 then d12 p else d2770 p
theorem agree2787 (p q : Pattern) (h : Agree support p q) : d2787 p = d2787 q := by
  simp only [d2787, h 138 (by decide), agree12 p q h, agree2770 p q h]
theorem nonnegative2787 (p : Pattern) : 0 ≤ d2787 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative2770 p)
def d2788 (p : Pattern) : Int := if p 116 then d2787 p else d2786 p
theorem agree2788 (p q : Pattern) (h : Agree support p q) : d2788 p = d2788 q := by
  simp only [d2788, h 116 (by decide), agree2787 p q h, agree2786 p q h]
theorem nonnegative2788 (p : Pattern) : 0 ≤ d2788 p :=
  nonnegative_ite (p 116) (nonnegative2787 p) (nonnegative2786 p)
def d2789 (p : Pattern) : Int := if p 115 then d2788 p else d2777 p
theorem agree2789 (p q : Pattern) (h : Agree support p q) : d2789 p = d2789 q := by
  simp only [d2789, h 115 (by decide), agree2788 p q h, agree2777 p q h]
theorem nonnegative2789 (p : Pattern) : 0 ≤ d2789 p :=
  nonnegative_ite (p 115) (nonnegative2788 p) (nonnegative2777 p)
def d2790 (p : Pattern) : Int := if p 71 then d2789 p else d2652 p
theorem agree2790 (p q : Pattern) (h : Agree support p q) : d2790 p = d2790 q := by
  simp only [d2790, h 71 (by decide), agree2789 p q h, agree2652 p q h]
theorem nonnegative2790 (p : Pattern) : 0 ≤ d2790 p :=
  nonnegative_ite (p 71) (nonnegative2789 p) (nonnegative2652 p)
def d2791 (p : Pattern) : Int := if p 49 then d2790 p else d2675 p
theorem agree2791 (p q : Pattern) (h : Agree support p q) : d2791 p = d2791 q := by
  simp only [d2791, h 49 (by decide), agree2790 p q h, agree2675 p q h]
theorem nonnegative2791 (p : Pattern) : 0 ≤ d2791 p :=
  nonnegative_ite (p 49) (nonnegative2790 p) (nonnegative2675 p)
def d2792 (p : Pattern) : Int := if p 182 then d2548 p else d2569 p
theorem agree2792 (p q : Pattern) (h : Agree support p q) : d2792 p = d2792 q := by
  simp only [d2792, h 182 (by decide), agree2548 p q h, agree2569 p q h]
theorem nonnegative2792 (p : Pattern) : 0 ≤ d2792 p :=
  nonnegative_ite (p 182) (nonnegative2548 p) (nonnegative2569 p)
def d2793 (p : Pattern) : Int := if p 163 then d2792 p else d2611 p
theorem agree2793 (p q : Pattern) (h : Agree support p q) : d2793 p = d2793 q := by
  simp only [d2793, h 163 (by decide), agree2792 p q h, agree2611 p q h]
theorem nonnegative2793 (p : Pattern) : 0 ≤ d2793 p :=
  nonnegative_ite (p 163) (nonnegative2792 p) (nonnegative2611 p)
def d2794 (p : Pattern) : Int := if p 182 then d2553 p else d2569 p
theorem agree2794 (p q : Pattern) (h : Agree support p q) : d2794 p = d2794 q := by
  simp only [d2794, h 182 (by decide), agree2553 p q h, agree2569 p q h]
theorem nonnegative2794 (p : Pattern) : 0 ≤ d2794 p :=
  nonnegative_ite (p 182) (nonnegative2553 p) (nonnegative2569 p)
def d2795 (p : Pattern) : Int := if p 182 then d12 p else d2612 p
theorem agree2795 (p q : Pattern) (h : Agree support p q) : d2795 p = d2795 q := by
  simp only [d2795, h 182 (by decide), agree12 p q h, agree2612 p q h]
theorem nonnegative2795 (p : Pattern) : 0 ≤ d2795 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2612 p)
def d2796 (p : Pattern) : Int := if p 163 then d2795 p else d2794 p
theorem agree2796 (p q : Pattern) (h : Agree support p q) : d2796 p = d2796 q := by
  simp only [d2796, h 163 (by decide), agree2795 p q h, agree2794 p q h]
theorem nonnegative2796 (p : Pattern) : 0 ≤ d2796 p :=
  nonnegative_ite (p 163) (nonnegative2795 p) (nonnegative2794 p)
def d2797 (p : Pattern) : Int := if p 162 then d2796 p else d2793 p
theorem agree2797 (p q : Pattern) (h : Agree support p q) : d2797 p = d2797 q := by
  simp only [d2797, h 162 (by decide), agree2796 p q h, agree2793 p q h]
theorem nonnegative2797 (p : Pattern) : 0 ≤ d2797 p :=
  nonnegative_ite (p 162) (nonnegative2796 p) (nonnegative2793 p)
def d2798 (p : Pattern) : Int := if p 163 then d2795 p else d2588 p
theorem agree2798 (p q : Pattern) (h : Agree support p q) : d2798 p = d2798 q := by
  simp only [d2798, h 163 (by decide), agree2795 p q h, agree2588 p q h]
theorem nonnegative2798 (p : Pattern) : 0 ≤ d2798 p :=
  nonnegative_ite (p 163) (nonnegative2795 p) (nonnegative2588 p)
def d2799 (p : Pattern) : Int := if p 162 then d2595 p else d2798 p
theorem agree2799 (p q : Pattern) (h : Agree support p q) : d2799 p = d2799 q := by
  simp only [d2799, h 162 (by decide), agree2595 p q h, agree2798 p q h]
theorem nonnegative2799 (p : Pattern) : 0 ≤ d2799 p :=
  nonnegative_ite (p 162) (nonnegative2595 p) (nonnegative2798 p)
def d2800 (p : Pattern) : Int := if p 161 then d2799 p else d2797 p
theorem agree2800 (p q : Pattern) (h : Agree support p q) : d2800 p = d2800 q := by
  simp only [d2800, h 161 (by decide), agree2799 p q h, agree2797 p q h]
theorem nonnegative2800 (p : Pattern) : 0 ≤ d2800 p :=
  nonnegative_ite (p 161) (nonnegative2799 p) (nonnegative2797 p)
def d2801 (p : Pattern) : Int := if p 160 then d2800 p else d2610 p
theorem agree2801 (p q : Pattern) (h : Agree support p q) : d2801 p = d2801 q := by
  simp only [d2801, h 160 (by decide), agree2800 p q h, agree2610 p q h]
theorem nonnegative2801 (p : Pattern) : 0 ≤ d2801 p :=
  nonnegative_ite (p 160) (nonnegative2800 p) (nonnegative2610 p)
def d2802 (p : Pattern) : Int := if p 163 then d2555 p else d2792 p
theorem agree2802 (p q : Pattern) (h : Agree support p q) : d2802 p = d2802 q := by
  simp only [d2802, h 163 (by decide), agree2555 p q h, agree2792 p q h]
theorem nonnegative2802 (p : Pattern) : 0 ≤ d2802 p :=
  nonnegative_ite (p 163) (nonnegative2555 p) (nonnegative2792 p)
def d2803 (p : Pattern) : Int := if p 163 then d2594 p else d2795 p
theorem agree2803 (p q : Pattern) (h : Agree support p q) : d2803 p = d2803 q := by
  simp only [d2803, h 163 (by decide), agree2594 p q h, agree2795 p q h]
theorem nonnegative2803 (p : Pattern) : 0 ≤ d2803 p :=
  nonnegative_ite (p 163) (nonnegative2594 p) (nonnegative2795 p)
def d2804 (p : Pattern) : Int := if p 162 then d2803 p else d2802 p
theorem agree2804 (p q : Pattern) (h : Agree support p q) : d2804 p = d2804 q := by
  simp only [d2804, h 162 (by decide), agree2803 p q h, agree2802 p q h]
theorem nonnegative2804 (p : Pattern) : 0 ≤ d2804 p :=
  nonnegative_ite (p 162) (nonnegative2803 p) (nonnegative2802 p)
def d2805 (p : Pattern) : Int := if p 163 then d12 p else d2795 p
theorem agree2805 (p q : Pattern) (h : Agree support p q) : d2805 p = d2805 q := by
  simp only [d2805, h 163 (by decide), agree12 p q h, agree2795 p q h]
theorem nonnegative2805 (p : Pattern) : 0 ≤ d2805 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2795 p)
def d2806 (p : Pattern) : Int := if p 162 then d12 p else d2805 p
theorem agree2806 (p q : Pattern) (h : Agree support p q) : d2806 p = d2806 q := by
  simp only [d2806, h 162 (by decide), agree12 p q h, agree2805 p q h]
theorem nonnegative2806 (p : Pattern) : 0 ≤ d2806 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2805 p)
def d2807 (p : Pattern) : Int := if p 161 then d2806 p else d2804 p
theorem agree2807 (p q : Pattern) (h : Agree support p q) : d2807 p = d2807 q := by
  simp only [d2807, h 161 (by decide), agree2806 p q h, agree2804 p q h]
theorem nonnegative2807 (p : Pattern) : 0 ≤ d2807 p :=
  nonnegative_ite (p 161) (nonnegative2806 p) (nonnegative2804 p)
def d2808 (p : Pattern) : Int := if p 160 then d2807 p else d2623 p
theorem agree2808 (p q : Pattern) (h : Agree support p q) : d2808 p = d2808 q := by
  simp only [d2808, h 160 (by decide), agree2807 p q h, agree2623 p q h]
theorem nonnegative2808 (p : Pattern) : 0 ≤ d2808 p :=
  nonnegative_ite (p 160) (nonnegative2807 p) (nonnegative2623 p)
def d2809 (p : Pattern) : Int := if p 141 then d2808 p else d2801 p
theorem agree2809 (p q : Pattern) (h : Agree support p q) : d2809 p = d2809 q := by
  simp only [d2809, h 141 (by decide), agree2808 p q h, agree2801 p q h]
theorem nonnegative2809 (p : Pattern) : 0 ≤ d2809 p :=
  nonnegative_ite (p 141) (nonnegative2808 p) (nonnegative2801 p)
def d2810 (p : Pattern) : Int := if p 162 then d2614 p else d2601 p
theorem agree2810 (p q : Pattern) (h : Agree support p q) : d2810 p = d2810 q := by
  simp only [d2810, h 162 (by decide), agree2614 p q h, agree2601 p q h]
theorem nonnegative2810 (p : Pattern) : 0 ≤ d2810 p :=
  nonnegative_ite (p 162) (nonnegative2614 p) (nonnegative2601 p)
def d2811 (p : Pattern) : Int := if p 161 then d2615 p else d2810 p
theorem agree2811 (p q : Pattern) (h : Agree support p q) : d2811 p = d2811 q := by
  simp only [d2811, h 161 (by decide), agree2615 p q h, agree2810 p q h]
theorem nonnegative2811 (p : Pattern) : 0 ≤ d2811 p :=
  nonnegative_ite (p 161) (nonnegative2615 p) (nonnegative2810 p)
def d2812 (p : Pattern) : Int := if p 225 then d12 p else d191 p
theorem agree2812 (p q : Pattern) (h : Agree support p q) : d2812 p = d2812 q := by
  simp only [d2812, h 225 (by decide), agree12 p q h, agree191 p q h]
theorem nonnegative2812 (p : Pattern) : 0 ≤ d2812 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative191 p)
def d2813 (p : Pattern) : Int := if p 224 then d320 p else d2812 p
theorem agree2813 (p q : Pattern) (h : Agree support p q) : d2813 p = d2813 q := by
  simp only [d2813, h 224 (by decide), agree320 p q h, agree2812 p q h]
theorem nonnegative2813 (p : Pattern) : 0 ≤ d2813 p :=
  nonnegative_ite (p 224) (nonnegative320 p) (nonnegative2812 p)
def d2814 (p : Pattern) : Int := if p 204 then d2813 p else d2812 p
theorem agree2814 (p q : Pattern) (h : Agree support p q) : d2814 p = d2814 q := by
  simp only [d2814, h 204 (by decide), agree2813 p q h, agree2812 p q h]
theorem nonnegative2814 (p : Pattern) : 0 ≤ d2814 p :=
  nonnegative_ite (p 204) (nonnegative2813 p) (nonnegative2812 p)
def d2815 (p : Pattern) : Int := if p 204 then d12 p else d2813 p
theorem agree2815 (p q : Pattern) (h : Agree support p q) : d2815 p = d2815 q := by
  simp only [d2815, h 204 (by decide), agree12 p q h, agree2813 p q h]
theorem nonnegative2815 (p : Pattern) : 0 ≤ d2815 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2813 p)
def d2816 (p : Pattern) : Int := if p 182 then d2815 p else d2814 p
theorem agree2816 (p q : Pattern) (h : Agree support p q) : d2816 p = d2816 q := by
  simp only [d2816, h 182 (by decide), agree2815 p q h, agree2814 p q h]
theorem nonnegative2816 (p : Pattern) : 0 ≤ d2816 p :=
  nonnegative_ite (p 182) (nonnegative2815 p) (nonnegative2814 p)
def d2817 (p : Pattern) : Int := if p 163 then d2816 p else d2603 p
theorem agree2817 (p q : Pattern) (h : Agree support p q) : d2817 p = d2817 q := by
  simp only [d2817, h 163 (by decide), agree2816 p q h, agree2603 p q h]
theorem nonnegative2817 (p : Pattern) : 0 ≤ d2817 p :=
  nonnegative_ite (p 163) (nonnegative2816 p) (nonnegative2603 p)
def d2818 (p : Pattern) : Int := if p 162 then d12 p else d2817 p
theorem agree2818 (p q : Pattern) (h : Agree support p q) : d2818 p = d2818 q := by
  simp only [d2818, h 162 (by decide), agree12 p q h, agree2817 p q h]
theorem nonnegative2818 (p : Pattern) : 0 ≤ d2818 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2817 p)
def d2819 (p : Pattern) : Int := if p 161 then d12 p else d2818 p
theorem agree2819 (p q : Pattern) (h : Agree support p q) : d2819 p = d2819 q := by
  simp only [d2819, h 161 (by decide), agree12 p q h, agree2818 p q h]
theorem nonnegative2819 (p : Pattern) : 0 ≤ d2819 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2818 p)
def d2820 (p : Pattern) : Int := if p 160 then d2819 p else d2811 p
theorem agree2820 (p q : Pattern) (h : Agree support p q) : d2820 p = d2820 q := by
  simp only [d2820, h 160 (by decide), agree2819 p q h, agree2811 p q h]
theorem nonnegative2820 (p : Pattern) : 0 ≤ d2820 p :=
  nonnegative_ite (p 160) (nonnegative2819 p) (nonnegative2811 p)
def d2821 (p : Pattern) : Int := if p 163 then d2584 p else d2603 p
theorem agree2821 (p q : Pattern) (h : Agree support p q) : d2821 p = d2821 q := by
  simp only [d2821, h 163 (by decide), agree2584 p q h, agree2603 p q h]
theorem nonnegative2821 (p : Pattern) : 0 ≤ d2821 p :=
  nonnegative_ite (p 163) (nonnegative2584 p) (nonnegative2603 p)
def d2822 (p : Pattern) : Int := if p 162 then d2821 p else d2611 p
theorem agree2822 (p q : Pattern) (h : Agree support p q) : d2822 p = d2822 q := by
  simp only [d2822, h 162 (by decide), agree2821 p q h, agree2611 p q h]
theorem nonnegative2822 (p : Pattern) : 0 ≤ d2822 p :=
  nonnegative_ite (p 162) (nonnegative2821 p) (nonnegative2611 p)
def d2823 (p : Pattern) : Int := if p 161 then d2625 p else d2822 p
theorem agree2823 (p q : Pattern) (h : Agree support p q) : d2823 p = d2823 q := by
  simp only [d2823, h 161 (by decide), agree2625 p q h, agree2822 p q h]
theorem nonnegative2823 (p : Pattern) : 0 ≤ d2823 p :=
  nonnegative_ite (p 161) (nonnegative2625 p) (nonnegative2822 p)
def d2824 (p : Pattern) : Int := if p 163 then d12 p else d2816 p
theorem agree2824 (p q : Pattern) (h : Agree support p q) : d2824 p = d2824 q := by
  simp only [d2824, h 163 (by decide), agree12 p q h, agree2816 p q h]
theorem nonnegative2824 (p : Pattern) : 0 ≤ d2824 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2816 p)
def d2825 (p : Pattern) : Int := if p 162 then d12 p else d2824 p
theorem agree2825 (p q : Pattern) (h : Agree support p q) : d2825 p = d2825 q := by
  simp only [d2825, h 162 (by decide), agree12 p q h, agree2824 p q h]
theorem nonnegative2825 (p : Pattern) : 0 ≤ d2825 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2824 p)
def d2826 (p : Pattern) : Int := if p 161 then d12 p else d2825 p
theorem agree2826 (p q : Pattern) (h : Agree support p q) : d2826 p = d2826 q := by
  simp only [d2826, h 161 (by decide), agree12 p q h, agree2825 p q h]
theorem nonnegative2826 (p : Pattern) : 0 ≤ d2826 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2825 p)
def d2827 (p : Pattern) : Int := if p 160 then d2826 p else d2823 p
theorem agree2827 (p q : Pattern) (h : Agree support p q) : d2827 p = d2827 q := by
  simp only [d2827, h 160 (by decide), agree2826 p q h, agree2823 p q h]
theorem nonnegative2827 (p : Pattern) : 0 ≤ d2827 p :=
  nonnegative_ite (p 160) (nonnegative2826 p) (nonnegative2823 p)
def d2828 (p : Pattern) : Int := if p 141 then d2827 p else d2820 p
theorem agree2828 (p q : Pattern) (h : Agree support p q) : d2828 p = d2828 q := by
  simp only [d2828, h 141 (by decide), agree2827 p q h, agree2820 p q h]
theorem nonnegative2828 (p : Pattern) : 0 ≤ d2828 p :=
  nonnegative_ite (p 141) (nonnegative2827 p) (nonnegative2820 p)
def d2829 (p : Pattern) : Int := if p 138 then d2828 p else d2809 p
theorem agree2829 (p q : Pattern) (h : Agree support p q) : d2829 p = d2829 q := by
  simp only [d2829, h 138 (by decide), agree2828 p q h, agree2809 p q h]
theorem nonnegative2829 (p : Pattern) : 0 ≤ d2829 p :=
  nonnegative_ite (p 138) (nonnegative2828 p) (nonnegative2809 p)
def d2830 (p : Pattern) : Int := if p 138 then d12 p else d2828 p
theorem agree2830 (p q : Pattern) (h : Agree support p q) : d2830 p = d2830 q := by
  simp only [d2830, h 138 (by decide), agree12 p q h, agree2828 p q h]
theorem nonnegative2830 (p : Pattern) : 0 ≤ d2830 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative2828 p)
def d2831 (p : Pattern) : Int := if p 116 then d2830 p else d2829 p
theorem agree2831 (p q : Pattern) (h : Agree support p q) : d2831 p = d2831 q := by
  simp only [d2831, h 116 (by decide), agree2830 p q h, agree2829 p q h]
theorem nonnegative2831 (p : Pattern) : 0 ≤ d2831 p :=
  nonnegative_ite (p 116) (nonnegative2830 p) (nonnegative2829 p)
def d2832 (p : Pattern) : Int := if p 115 then d2831 p else d2667 p
theorem agree2832 (p q : Pattern) (h : Agree support p q) : d2832 p = d2832 q := by
  simp only [d2832, h 115 (by decide), agree2831 p q h, agree2667 p q h]
theorem nonnegative2832 (p : Pattern) : 0 ≤ d2832 p :=
  nonnegative_ite (p 115) (nonnegative2831 p) (nonnegative2667 p)
def d2833 (p : Pattern) : Int := if p 71 then d2832 p else d2652 p
theorem agree2833 (p q : Pattern) (h : Agree support p q) : d2833 p = d2833 q := by
  simp only [d2833, h 71 (by decide), agree2832 p q h, agree2652 p q h]
theorem nonnegative2833 (p : Pattern) : 0 ≤ d2833 p :=
  nonnegative_ite (p 71) (nonnegative2832 p) (nonnegative2652 p)
def d2834 (p : Pattern) : Int := if p 163 then d12 p else d2696 p
theorem agree2834 (p q : Pattern) (h : Agree support p q) : d2834 p = d2834 q := by
  simp only [d2834, h 163 (by decide), agree12 p q h, agree2696 p q h]
theorem nonnegative2834 (p : Pattern) : 0 ≤ d2834 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2696 p)
def d2835 (p : Pattern) : Int := if p 162 then d2834 p else d2730 p
theorem agree2835 (p q : Pattern) (h : Agree support p q) : d2835 p = d2835 q := by
  simp only [d2835, h 162 (by decide), agree2834 p q h, agree2730 p q h]
theorem nonnegative2835 (p : Pattern) : 0 ≤ d2835 p :=
  nonnegative_ite (p 162) (nonnegative2834 p) (nonnegative2730 p)
def d2836 (p : Pattern) : Int := if p 162 then d12 p else d2834 p
theorem agree2836 (p q : Pattern) (h : Agree support p q) : d2836 p = d2836 q := by
  simp only [d2836, h 162 (by decide), agree12 p q h, agree2834 p q h]
theorem nonnegative2836 (p : Pattern) : 0 ≤ d2836 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2834 p)
def d2837 (p : Pattern) : Int := if p 161 then d2836 p else d2835 p
theorem agree2837 (p q : Pattern) (h : Agree support p q) : d2837 p = d2837 q := by
  simp only [d2837, h 161 (by decide), agree2836 p q h, agree2835 p q h]
theorem nonnegative2837 (p : Pattern) : 0 ≤ d2837 p :=
  nonnegative_ite (p 161) (nonnegative2836 p) (nonnegative2835 p)
def d2838 (p : Pattern) : Int := if p 163 then d12 p else d2714 p
theorem agree2838 (p q : Pattern) (h : Agree support p q) : d2838 p = d2838 q := by
  simp only [d2838, h 163 (by decide), agree12 p q h, agree2714 p q h]
theorem nonnegative2838 (p : Pattern) : 0 ≤ d2838 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2714 p)
def d2839 (p : Pattern) : Int := if p 162 then d2838 p else d2737 p
theorem agree2839 (p q : Pattern) (h : Agree support p q) : d2839 p = d2839 q := by
  simp only [d2839, h 162 (by decide), agree2838 p q h, agree2737 p q h]
theorem nonnegative2839 (p : Pattern) : 0 ≤ d2839 p :=
  nonnegative_ite (p 162) (nonnegative2838 p) (nonnegative2737 p)
def d2840 (p : Pattern) : Int := if p 162 then d12 p else d2838 p
theorem agree2840 (p q : Pattern) (h : Agree support p q) : d2840 p = d2840 q := by
  simp only [d2840, h 162 (by decide), agree12 p q h, agree2838 p q h]
theorem nonnegative2840 (p : Pattern) : 0 ≤ d2840 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2838 p)
def d2841 (p : Pattern) : Int := if p 161 then d2840 p else d2839 p
theorem agree2841 (p q : Pattern) (h : Agree support p q) : d2841 p = d2841 q := by
  simp only [d2841, h 161 (by decide), agree2840 p q h, agree2839 p q h]
theorem nonnegative2841 (p : Pattern) : 0 ≤ d2841 p :=
  nonnegative_ite (p 161) (nonnegative2840 p) (nonnegative2839 p)
def d2842 (p : Pattern) : Int := if p 160 then d2841 p else d2837 p
theorem agree2842 (p q : Pattern) (h : Agree support p q) : d2842 p = d2842 q := by
  simp only [d2842, h 160 (by decide), agree2841 p q h, agree2837 p q h]
theorem nonnegative2842 (p : Pattern) : 0 ≤ d2842 p :=
  nonnegative_ite (p 160) (nonnegative2841 p) (nonnegative2837 p)
def d2843 (p : Pattern) : Int := if p 141 then d2842 p else d2720 p
theorem agree2843 (p q : Pattern) (h : Agree support p q) : d2843 p = d2843 q := by
  simp only [d2843, h 141 (by decide), agree2842 p q h, agree2720 p q h]
theorem nonnegative2843 (p : Pattern) : 0 ≤ d2843 p :=
  nonnegative_ite (p 141) (nonnegative2842 p) (nonnegative2720 p)
def d2844 (p : Pattern) : Int := if p 163 then d12 p else d2748 p
theorem agree2844 (p q : Pattern) (h : Agree support p q) : d2844 p = d2844 q := by
  simp only [d2844, h 163 (by decide), agree12 p q h, agree2748 p q h]
theorem nonnegative2844 (p : Pattern) : 0 ≤ d2844 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2748 p)
def d2845 (p : Pattern) : Int := if p 162 then d2844 p else d2760 p
theorem agree2845 (p q : Pattern) (h : Agree support p q) : d2845 p = d2845 q := by
  simp only [d2845, h 162 (by decide), agree2844 p q h, agree2760 p q h]
theorem nonnegative2845 (p : Pattern) : 0 ≤ d2845 p :=
  nonnegative_ite (p 162) (nonnegative2844 p) (nonnegative2760 p)
def d2846 (p : Pattern) : Int := if p 162 then d12 p else d2844 p
theorem agree2846 (p q : Pattern) (h : Agree support p q) : d2846 p = d2846 q := by
  simp only [d2846, h 162 (by decide), agree12 p q h, agree2844 p q h]
theorem nonnegative2846 (p : Pattern) : 0 ≤ d2846 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2844 p)
def d2847 (p : Pattern) : Int := if p 161 then d2846 p else d2845 p
theorem agree2847 (p q : Pattern) (h : Agree support p q) : d2847 p = d2847 q := by
  simp only [d2847, h 161 (by decide), agree2846 p q h, agree2845 p q h]
theorem nonnegative2847 (p : Pattern) : 0 ≤ d2847 p :=
  nonnegative_ite (p 161) (nonnegative2846 p) (nonnegative2845 p)
def d2848 (p : Pattern) : Int := if p 160 then d2768 p else d2847 p
theorem agree2848 (p q : Pattern) (h : Agree support p q) : d2848 p = d2848 q := by
  simp only [d2848, h 160 (by decide), agree2768 p q h, agree2847 p q h]
theorem nonnegative2848 (p : Pattern) : 0 ≤ d2848 p :=
  nonnegative_ite (p 160) (nonnegative2768 p) (nonnegative2847 p)
def d2849 (p : Pattern) : Int := if p 141 then d2848 p else d2759 p
theorem agree2849 (p q : Pattern) (h : Agree support p q) : d2849 p = d2849 q := by
  simp only [d2849, h 141 (by decide), agree2848 p q h, agree2759 p q h]
theorem nonnegative2849 (p : Pattern) : 0 ≤ d2849 p :=
  nonnegative_ite (p 141) (nonnegative2848 p) (nonnegative2759 p)
def d2850 (p : Pattern) : Int := if p 138 then d2849 p else d2843 p
theorem agree2850 (p q : Pattern) (h : Agree support p q) : d2850 p = d2850 q := by
  simp only [d2850, h 138 (by decide), agree2849 p q h, agree2843 p q h]
theorem nonnegative2850 (p : Pattern) : 0 ≤ d2850 p :=
  nonnegative_ite (p 138) (nonnegative2849 p) (nonnegative2843 p)
def d2851 (p : Pattern) : Int := if p 138 then d2775 p else d2849 p
theorem agree2851 (p q : Pattern) (h : Agree support p q) : d2851 p = d2851 q := by
  simp only [d2851, h 138 (by decide), agree2775 p q h, agree2849 p q h]
theorem nonnegative2851 (p : Pattern) : 0 ≤ d2851 p :=
  nonnegative_ite (p 138) (nonnegative2775 p) (nonnegative2849 p)
def d2852 (p : Pattern) : Int := if p 116 then d2851 p else d2850 p
theorem agree2852 (p q : Pattern) (h : Agree support p q) : d2852 p = d2852 q := by
  simp only [d2852, h 116 (by decide), agree2851 p q h, agree2850 p q h]
theorem nonnegative2852 (p : Pattern) : 0 ≤ d2852 p :=
  nonnegative_ite (p 116) (nonnegative2851 p) (nonnegative2850 p)
def d2853 (p : Pattern) : Int := if p 182 then d2710 p else d2725 p
theorem agree2853 (p q : Pattern) (h : Agree support p q) : d2853 p = d2853 q := by
  simp only [d2853, h 182 (by decide), agree2710 p q h, agree2725 p q h]
theorem nonnegative2853 (p : Pattern) : 0 ≤ d2853 p :=
  nonnegative_ite (p 182) (nonnegative2710 p) (nonnegative2725 p)
def d2854 (p : Pattern) : Int := if p 163 then d2853 p else d2753 p
theorem agree2854 (p q : Pattern) (h : Agree support p q) : d2854 p = d2854 q := by
  simp only [d2854, h 163 (by decide), agree2853 p q h, agree2753 p q h]
theorem nonnegative2854 (p : Pattern) : 0 ≤ d2854 p :=
  nonnegative_ite (p 163) (nonnegative2853 p) (nonnegative2753 p)
def d2855 (p : Pattern) : Int := if p 162 then d2838 p else d2854 p
theorem agree2855 (p q : Pattern) (h : Agree support p q) : d2855 p = d2855 q := by
  simp only [d2855, h 162 (by decide), agree2838 p q h, agree2854 p q h]
theorem nonnegative2855 (p : Pattern) : 0 ≤ d2855 p :=
  nonnegative_ite (p 162) (nonnegative2838 p) (nonnegative2854 p)
def d2856 (p : Pattern) : Int := if p 182 then d12 p else d2754 p
theorem agree2856 (p q : Pattern) (h : Agree support p q) : d2856 p = d2856 q := by
  simp only [d2856, h 182 (by decide), agree12 p q h, agree2754 p q h]
theorem nonnegative2856 (p : Pattern) : 0 ≤ d2856 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2754 p)
def d2857 (p : Pattern) : Int := if p 163 then d12 p else d2856 p
theorem agree2857 (p q : Pattern) (h : Agree support p q) : d2857 p = d2857 q := by
  simp only [d2857, h 163 (by decide), agree12 p q h, agree2856 p q h]
theorem nonnegative2857 (p : Pattern) : 0 ≤ d2857 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2856 p)
def d2858 (p : Pattern) : Int := if p 162 then d12 p else d2857 p
theorem agree2858 (p q : Pattern) (h : Agree support p q) : d2858 p = d2858 q := by
  simp only [d2858, h 162 (by decide), agree12 p q h, agree2857 p q h]
theorem nonnegative2858 (p : Pattern) : 0 ≤ d2858 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2857 p)
def d2859 (p : Pattern) : Int := if p 161 then d2858 p else d2855 p
theorem agree2859 (p q : Pattern) (h : Agree support p q) : d2859 p = d2859 q := by
  simp only [d2859, h 161 (by decide), agree2858 p q h, agree2855 p q h]
theorem nonnegative2859 (p : Pattern) : 0 ≤ d2859 p :=
  nonnegative_ite (p 161) (nonnegative2858 p) (nonnegative2855 p)
def d2860 (p : Pattern) : Int := if p 160 then d2859 p else d2752 p
theorem agree2860 (p q : Pattern) (h : Agree support p q) : d2860 p = d2860 q := by
  simp only [d2860, h 160 (by decide), agree2859 p q h, agree2752 p q h]
theorem nonnegative2860 (p : Pattern) : 0 ≤ d2860 p :=
  nonnegative_ite (p 160) (nonnegative2859 p) (nonnegative2752 p)
def d2861 (p : Pattern) : Int := if p 182 then d2710 p else d2692 p
theorem agree2861 (p q : Pattern) (h : Agree support p q) : d2861 p = d2861 q := by
  simp only [d2861, h 182 (by decide), agree2710 p q h, agree2692 p q h]
theorem nonnegative2861 (p : Pattern) : 0 ≤ d2861 p :=
  nonnegative_ite (p 182) (nonnegative2710 p) (nonnegative2692 p)
def d2862 (p : Pattern) : Int := if p 163 then d2714 p else d2861 p
theorem agree2862 (p q : Pattern) (h : Agree support p q) : d2862 p = d2862 q := by
  simp only [d2862, h 163 (by decide), agree2714 p q h, agree2861 p q h]
theorem nonnegative2862 (p : Pattern) : 0 ≤ d2862 p :=
  nonnegative_ite (p 163) (nonnegative2714 p) (nonnegative2861 p)
def d2863 (p : Pattern) : Int := if p 162 then d2857 p else d2862 p
theorem agree2863 (p q : Pattern) (h : Agree support p q) : d2863 p = d2863 q := by
  simp only [d2863, h 162 (by decide), agree2857 p q h, agree2862 p q h]
theorem nonnegative2863 (p : Pattern) : 0 ≤ d2863 p :=
  nonnegative_ite (p 162) (nonnegative2857 p) (nonnegative2862 p)
def d2864 (p : Pattern) : Int := if p 162 then d12 p else d2561 p
theorem agree2864 (p q : Pattern) (h : Agree support p q) : d2864 p = d2864 q := by
  simp only [d2864, h 162 (by decide), agree12 p q h, agree2561 p q h]
theorem nonnegative2864 (p : Pattern) : 0 ≤ d2864 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2561 p)
def d2865 (p : Pattern) : Int := if p 161 then d2864 p else d2863 p
theorem agree2865 (p q : Pattern) (h : Agree support p q) : d2865 p = d2865 q := by
  simp only [d2865, h 161 (by decide), agree2864 p q h, agree2863 p q h]
theorem nonnegative2865 (p : Pattern) : 0 ≤ d2865 p :=
  nonnegative_ite (p 161) (nonnegative2864 p) (nonnegative2863 p)
def d2866 (p : Pattern) : Int := if p 160 then d2865 p else d2847 p
theorem agree2866 (p q : Pattern) (h : Agree support p q) : d2866 p = d2866 q := by
  simp only [d2866, h 160 (by decide), agree2865 p q h, agree2847 p q h]
theorem nonnegative2866 (p : Pattern) : 0 ≤ d2866 p :=
  nonnegative_ite (p 160) (nonnegative2865 p) (nonnegative2847 p)
def d2867 (p : Pattern) : Int := if p 141 then d2866 p else d2860 p
theorem agree2867 (p q : Pattern) (h : Agree support p q) : d2867 p = d2867 q := by
  simp only [d2867, h 141 (by decide), agree2866 p q h, agree2860 p q h]
theorem nonnegative2867 (p : Pattern) : 0 ≤ d2867 p :=
  nonnegative_ite (p 141) (nonnegative2866 p) (nonnegative2860 p)
def d2868 (p : Pattern) : Int := if p 163 then d2584 p else d2753 p
theorem agree2868 (p q : Pattern) (h : Agree support p q) : d2868 p = d2868 q := by
  simp only [d2868, h 163 (by decide), agree2584 p q h, agree2753 p q h]
theorem nonnegative2868 (p : Pattern) : 0 ≤ d2868 p :=
  nonnegative_ite (p 163) (nonnegative2584 p) (nonnegative2753 p)
def d2869 (p : Pattern) : Int := if p 162 then d2868 p else d2746 p
theorem agree2869 (p q : Pattern) (h : Agree support p q) : d2869 p = d2869 q := by
  simp only [d2869, h 162 (by decide), agree2868 p q h, agree2746 p q h]
theorem nonnegative2869 (p : Pattern) : 0 ≤ d2869 p :=
  nonnegative_ite (p 162) (nonnegative2868 p) (nonnegative2746 p)
def d2870 (p : Pattern) : Int := if p 161 then d2764 p else d2869 p
theorem agree2870 (p q : Pattern) (h : Agree support p q) : d2870 p = d2870 q := by
  simp only [d2870, h 161 (by decide), agree2764 p q h, agree2869 p q h]
theorem nonnegative2870 (p : Pattern) : 0 ≤ d2870 p :=
  nonnegative_ite (p 161) (nonnegative2764 p) (nonnegative2869 p)
def d2871 (p : Pattern) : Int := if p 160 then d2768 p else d2870 p
theorem agree2871 (p q : Pattern) (h : Agree support p q) : d2871 p = d2871 q := by
  simp only [d2871, h 160 (by decide), agree2768 p q h, agree2870 p q h]
theorem nonnegative2871 (p : Pattern) : 0 ≤ d2871 p :=
  nonnegative_ite (p 160) (nonnegative2768 p) (nonnegative2870 p)
def d2872 (p : Pattern) : Int := if p 162 then d2844 p else d2753 p
theorem agree2872 (p q : Pattern) (h : Agree support p q) : d2872 p = d2872 q := by
  simp only [d2872, h 162 (by decide), agree2844 p q h, agree2753 p q h]
theorem nonnegative2872 (p : Pattern) : 0 ≤ d2872 p :=
  nonnegative_ite (p 162) (nonnegative2844 p) (nonnegative2753 p)
def d2873 (p : Pattern) : Int := if p 161 then d2767 p else d2872 p
theorem agree2873 (p q : Pattern) (h : Agree support p q) : d2873 p = d2873 q := by
  simp only [d2873, h 161 (by decide), agree2767 p q h, agree2872 p q h]
theorem nonnegative2873 (p : Pattern) : 0 ≤ d2873 p :=
  nonnegative_ite (p 161) (nonnegative2767 p) (nonnegative2872 p)
def d2874 (p : Pattern) : Int := if p 162 then d12 p else d2608 p
theorem agree2874 (p q : Pattern) (h : Agree support p q) : d2874 p = d2874 q := by
  simp only [d2874, h 162 (by decide), agree12 p q h, agree2608 p q h]
theorem nonnegative2874 (p : Pattern) : 0 ≤ d2874 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2608 p)
def d2875 (p : Pattern) : Int := if p 161 then d12 p else d2874 p
theorem agree2875 (p q : Pattern) (h : Agree support p q) : d2875 p = d2875 q := by
  simp only [d2875, h 161 (by decide), agree12 p q h, agree2874 p q h]
theorem nonnegative2875 (p : Pattern) : 0 ≤ d2875 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2874 p)
def d2876 (p : Pattern) : Int := if p 160 then d2875 p else d2873 p
theorem agree2876 (p q : Pattern) (h : Agree support p q) : d2876 p = d2876 q := by
  simp only [d2876, h 160 (by decide), agree2875 p q h, agree2873 p q h]
theorem nonnegative2876 (p : Pattern) : 0 ≤ d2876 p :=
  nonnegative_ite (p 160) (nonnegative2875 p) (nonnegative2873 p)
def d2877 (p : Pattern) : Int := if p 141 then d2876 p else d2871 p
theorem agree2877 (p q : Pattern) (h : Agree support p q) : d2877 p = d2877 q := by
  simp only [d2877, h 141 (by decide), agree2876 p q h, agree2871 p q h]
theorem nonnegative2877 (p : Pattern) : 0 ≤ d2877 p :=
  nonnegative_ite (p 141) (nonnegative2876 p) (nonnegative2871 p)
def d2878 (p : Pattern) : Int := if p 138 then d2877 p else d2867 p
theorem agree2878 (p q : Pattern) (h : Agree support p q) : d2878 p = d2878 q := by
  simp only [d2878, h 138 (by decide), agree2877 p q h, agree2867 p q h]
theorem nonnegative2878 (p : Pattern) : 0 ≤ d2878 p :=
  nonnegative_ite (p 138) (nonnegative2877 p) (nonnegative2867 p)
def d2879 (p : Pattern) : Int := if p 163 then d2607 p else d2753 p
theorem agree2879 (p q : Pattern) (h : Agree support p q) : d2879 p = d2879 q := by
  simp only [d2879, h 163 (by decide), agree2607 p q h, agree2753 p q h]
theorem nonnegative2879 (p : Pattern) : 0 ≤ d2879 p :=
  nonnegative_ite (p 163) (nonnegative2607 p) (nonnegative2753 p)
end NetHack.Sokoban22Refined85
