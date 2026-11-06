/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions82
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub9960 (p : Pattern) : d2800 (change p 225 none) = d5748 p := by
  change (if p 161 then d2799 (change p 225 none) else d2797 (change p 225 none)) = d5748 p
  rw [sub9959, sub9957]
  rfl
theorem sub9961 (p : Pattern) : d2801 (change p 225 none) = d5749 p := by
  change (if p 160 then d2800 (change p 225 none) else d2610 (change p 225 none)) = d5749 p
  rw [sub9960, sub9744]
  rfl
theorem sub9962 (p : Pattern) : d2802 (change p 225 none) = d5750 p := by
  change (if p 163 then d2555 (change p 225 none) else d2792 (change p 225 none)) = d5750 p
  rw [sub9684, sub9952]
  rfl
theorem sub9963 (p : Pattern) : d2803 (change p 225 none) = d5751 p := by
  change (if p 163 then d2594 (change p 225 none) else d2795 (change p 225 none)) = d5751 p
  rw [sub9728, sub9955]
  rfl
theorem sub9964 (p : Pattern) : d2804 (change p 225 none) = d5752 p := by
  change (if p 162 then d2803 (change p 225 none) else d2802 (change p 225 none)) = d5752 p
  rw [sub9963, sub9962]
  rfl
theorem sub9965 (p : Pattern) : d2805 (change p 225 none) = d5753 p := by
  change (if p 163 then d12 (change p 225 none) else d2795 (change p 225 none)) = d5753 p
  rw [sub9592, sub9955]
  rfl
theorem sub9966 (p : Pattern) : d2806 (change p 225 none) = d5754 p := by
  change (if p 162 then d12 (change p 225 none) else d2805 (change p 225 none)) = d5754 p
  rw [sub9592, sub9965]
  rfl
theorem sub9967 (p : Pattern) : d2807 (change p 225 none) = d5755 p := by
  change (if p 161 then d2806 (change p 225 none) else d2804 (change p 225 none)) = d5755 p
  rw [sub9966, sub9964]
  rfl
theorem sub9968 (p : Pattern) : d2808 (change p 225 none) = d5756 p := by
  change (if p 160 then d2807 (change p 225 none) else d2623 (change p 225 none)) = d5756 p
  rw [sub9967, sub9757]
  rfl
theorem sub9969 (p : Pattern) : d2809 (change p 225 none) = d5757 p := by
  change (if p 141 then d2808 (change p 225 none) else d2801 (change p 225 none)) = d5757 p
  rw [sub9968, sub9961]
  rfl
theorem sub9970 (p : Pattern) : d2810 (change p 225 none) = d5758 p := by
  change (if p 162 then d2614 (change p 225 none) else d2601 (change p 225 none)) = d5758 p
  rw [sub9748, sub9735]
  rfl
theorem sub9971 (p : Pattern) : d2811 (change p 225 none) = d5759 p := by
  change (if p 161 then d2615 (change p 225 none) else d2810 (change p 225 none)) = d5759 p
  rw [sub9749, sub9970]
  rfl
theorem sub9972 (p : Pattern) : d191 (change p 225 none) = d191 p := by
  change (if p 246 then d190 (change p 225 none) else d8 (change p 225 none)) = d191 p
  rw [sub9624, sub9622]
  rfl
theorem sub9973 (p : Pattern) : d2812 (change p 225 none) = d191 p := by
  change d191 (change p 225 none) = d191 p
  exact sub9972 p
theorem sub9974 (p : Pattern) : d315 (change p 225 none) = d315 p := by
  change (if p 246 then d12 (change p 225 none) else d190 (change p 225 none)) = d315 p
  rw [sub9592, sub9624]
  rfl
theorem sub9975 (p : Pattern) : d320 (change p 225 none) = d315 p := by
  change d315 (change p 225 none) = d315 p
  exact sub9974 p
theorem sub9976 (p : Pattern) : d2813 (change p 225 none) = d5760 p := by
  change (if p 224 then d320 (change p 225 none) else d2812 (change p 225 none)) = d5760 p
  rw [sub9975, sub9973]
  rfl
theorem sub9977 (p : Pattern) : d2814 (change p 225 none) = d5761 p := by
  change (if p 204 then d2813 (change p 225 none) else d2812 (change p 225 none)) = d5761 p
  rw [sub9976, sub9973]
  rfl
theorem sub9978 (p : Pattern) : d2815 (change p 225 none) = d5762 p := by
  change (if p 204 then d12 (change p 225 none) else d2813 (change p 225 none)) = d5762 p
  rw [sub9592, sub9976]
  rfl
theorem sub9979 (p : Pattern) : d2816 (change p 225 none) = d5763 p := by
  change (if p 182 then d2815 (change p 225 none) else d2814 (change p 225 none)) = d5763 p
  rw [sub9978, sub9977]
  rfl
theorem sub9980 (p : Pattern) : d2817 (change p 225 none) = d5764 p := by
  change (if p 163 then d2816 (change p 225 none) else d2603 (change p 225 none)) = d5764 p
  rw [sub9979, sub9737]
  rfl
theorem sub9981 (p : Pattern) : d2818 (change p 225 none) = d5765 p := by
  change (if p 162 then d12 (change p 225 none) else d2817 (change p 225 none)) = d5765 p
  rw [sub9592, sub9980]
  rfl
theorem sub9982 (p : Pattern) : d2819 (change p 225 none) = d5766 p := by
  change (if p 161 then d12 (change p 225 none) else d2818 (change p 225 none)) = d5766 p
  rw [sub9592, sub9981]
  rfl
theorem sub9983 (p : Pattern) : d2820 (change p 225 none) = d5767 p := by
  change (if p 160 then d2819 (change p 225 none) else d2811 (change p 225 none)) = d5767 p
  rw [sub9982, sub9971]
  rfl
theorem sub9984 (p : Pattern) : d2821 (change p 225 none) = d5768 p := by
  change (if p 163 then d2584 (change p 225 none) else d2603 (change p 225 none)) = d5768 p
  rw [sub9718, sub9737]
  rfl
theorem sub9985 (p : Pattern) : d2822 (change p 225 none) = d5769 p := by
  change (if p 162 then d2821 (change p 225 none) else d2611 (change p 225 none)) = d5769 p
  rw [sub9984, sub9745]
  rfl
theorem sub9986 (p : Pattern) : d2823 (change p 225 none) = d5770 p := by
  change (if p 161 then d2625 (change p 225 none) else d2822 (change p 225 none)) = d5770 p
  rw [sub9759, sub9985]
  rfl
theorem sub9987 (p : Pattern) : d2824 (change p 225 none) = d5771 p := by
  change (if p 163 then d12 (change p 225 none) else d2816 (change p 225 none)) = d5771 p
  rw [sub9592, sub9979]
  rfl
theorem sub9988 (p : Pattern) : d2825 (change p 225 none) = d5772 p := by
  change (if p 162 then d12 (change p 225 none) else d2824 (change p 225 none)) = d5772 p
  rw [sub9592, sub9987]
  rfl
theorem sub9989 (p : Pattern) : d2826 (change p 225 none) = d5773 p := by
  change (if p 161 then d12 (change p 225 none) else d2825 (change p 225 none)) = d5773 p
  rw [sub9592, sub9988]
  rfl
theorem sub9990 (p : Pattern) : d2827 (change p 225 none) = d5774 p := by
  change (if p 160 then d2826 (change p 225 none) else d2823 (change p 225 none)) = d5774 p
  rw [sub9989, sub9986]
  rfl
theorem sub9991 (p : Pattern) : d2828 (change p 225 none) = d5775 p := by
  change (if p 141 then d2827 (change p 225 none) else d2820 (change p 225 none)) = d5775 p
  rw [sub9990, sub9983]
  rfl
theorem sub9992 (p : Pattern) : d2829 (change p 225 none) = d5776 p := by
  change (if p 138 then d2828 (change p 225 none) else d2809 (change p 225 none)) = d5776 p
  rw [sub9991, sub9969]
  rfl
theorem sub9993 (p : Pattern) : d2830 (change p 225 none) = d5777 p := by
  change (if p 138 then d12 (change p 225 none) else d2828 (change p 225 none)) = d5777 p
  rw [sub9592, sub9991]
  rfl
theorem sub9994 (p : Pattern) : d2831 (change p 225 none) = d5778 p := by
  change (if p 116 then d2830 (change p 225 none) else d2829 (change p 225 none)) = d5778 p
  rw [sub9993, sub9992]
  rfl
theorem sub9995 (p : Pattern) : d2832 (change p 225 none) = d5779 p := by
  change (if p 115 then d2831 (change p 225 none) else d2667 (change p 225 none)) = d5779 p
  rw [sub9994, sub9801]
  rfl
theorem sub9996 (p : Pattern) : d2833 (change p 225 none) = d5780 p := by
  change (if p 71 then d2832 (change p 225 none) else d2652 (change p 225 none)) = d5780 p
  rw [sub9995, sub9786]
  rfl
theorem sub9997 (p : Pattern) : d2834 (change p 225 none) = d5781 p := by
  change (if p 163 then d12 (change p 225 none) else d2696 (change p 225 none)) = d5781 p
  rw [sub9592, sub9848]
  rfl
theorem sub9998 (p : Pattern) : d2835 (change p 225 none) = d5782 p := by
  change (if p 162 then d2834 (change p 225 none) else d2730 (change p 225 none)) = d5782 p
  rw [sub9997, sub9890]
  rfl
theorem sub9999 (p : Pattern) : d2836 (change p 225 none) = d5783 p := by
  change (if p 162 then d12 (change p 225 none) else d2834 (change p 225 none)) = d5783 p
  rw [sub9592, sub9997]
  rfl
theorem sub10000 (p : Pattern) : d2837 (change p 225 none) = d5784 p := by
  change (if p 161 then d2836 (change p 225 none) else d2835 (change p 225 none)) = d5784 p
  rw [sub9999, sub9998]
  rfl
theorem sub10001 (p : Pattern) : d2838 (change p 225 none) = d5785 p := by
  change (if p 163 then d12 (change p 225 none) else d2714 (change p 225 none)) = d5785 p
  rw [sub9592, sub9872]
  rfl
theorem sub10002 (p : Pattern) : d2839 (change p 225 none) = d5786 p := by
  change (if p 162 then d2838 (change p 225 none) else d2737 (change p 225 none)) = d5786 p
  rw [sub10001, sub9897]
  rfl
theorem sub10003 (p : Pattern) : d2840 (change p 225 none) = d5787 p := by
  change (if p 162 then d12 (change p 225 none) else d2838 (change p 225 none)) = d5787 p
  rw [sub9592, sub10001]
  rfl
theorem sub10004 (p : Pattern) : d2841 (change p 225 none) = d5788 p := by
  change (if p 161 then d2840 (change p 225 none) else d2839 (change p 225 none)) = d5788 p
  rw [sub10003, sub10002]
  rfl
theorem sub10005 (p : Pattern) : d2842 (change p 225 none) = d5789 p := by
  change (if p 160 then d2841 (change p 225 none) else d2837 (change p 225 none)) = d5789 p
  rw [sub10004, sub10000]
  rfl
theorem sub10006 (p : Pattern) : d2843 (change p 225 none) = d5790 p := by
  change (if p 141 then d2842 (change p 225 none) else d2720 (change p 225 none)) = d5790 p
  rw [sub10005, sub9878]
  rfl
theorem sub10007 (p : Pattern) : d2844 (change p 225 none) = d5791 p := by
  change (if p 163 then d12 (change p 225 none) else d2748 (change p 225 none)) = d5791 p
  rw [sub9592, sub9908]
  rfl
theorem sub10008 (p : Pattern) : d2845 (change p 225 none) = d5792 p := by
  change (if p 162 then d2844 (change p 225 none) else d2760 (change p 225 none)) = d5792 p
  rw [sub10007, sub9920]
  rfl
theorem sub10009 (p : Pattern) : d2846 (change p 225 none) = d5793 p := by
  change (if p 162 then d12 (change p 225 none) else d2844 (change p 225 none)) = d5793 p
  rw [sub9592, sub10007]
  rfl
theorem sub10010 (p : Pattern) : d2847 (change p 225 none) = d5794 p := by
  change (if p 161 then d2846 (change p 225 none) else d2845 (change p 225 none)) = d5794 p
  rw [sub10009, sub10008]
  rfl
theorem sub10011 (p : Pattern) : d2848 (change p 225 none) = d5795 p := by
  change (if p 160 then d2768 (change p 225 none) else d2847 (change p 225 none)) = d5795 p
  rw [sub9928, sub10010]
  rfl
theorem sub10012 (p : Pattern) : d2849 (change p 225 none) = d5796 p := by
  change (if p 141 then d2848 (change p 225 none) else d2759 (change p 225 none)) = d5796 p
  rw [sub10011, sub9919]
  rfl
theorem sub10013 (p : Pattern) : d2850 (change p 225 none) = d5797 p := by
  change (if p 138 then d2849 (change p 225 none) else d2843 (change p 225 none)) = d5797 p
  rw [sub10012, sub10006]
  rfl
theorem sub10014 (p : Pattern) : d2851 (change p 225 none) = d5798 p := by
  change (if p 138 then d2775 (change p 225 none) else d2849 (change p 225 none)) = d5798 p
  rw [sub9935, sub10012]
  rfl
theorem sub10015 (p : Pattern) : d2852 (change p 225 none) = d5799 p := by
  change (if p 116 then d2851 (change p 225 none) else d2850 (change p 225 none)) = d5799 p
  rw [sub10014, sub10013]
  rfl
theorem sub10016 (p : Pattern) : d2853 (change p 225 none) = d5800 p := by
  change (if p 182 then d2710 (change p 225 none) else d2725 (change p 225 none)) = d5800 p
  rw [sub9868, sub9883]
  rfl
theorem sub10017 (p : Pattern) : d2854 (change p 225 none) = d5801 p := by
  change (if p 163 then d2853 (change p 225 none) else d2753 (change p 225 none)) = d5801 p
  rw [sub10016, sub9913]
  rfl
theorem sub10018 (p : Pattern) : d2855 (change p 225 none) = d5802 p := by
  change (if p 162 then d2838 (change p 225 none) else d2854 (change p 225 none)) = d5802 p
  rw [sub10001, sub10017]
  rfl
theorem sub10019 (p : Pattern) : d2856 (change p 225 none) = d5803 p := by
  change (if p 182 then d12 (change p 225 none) else d2754 (change p 225 none)) = d5803 p
  rw [sub9592, sub9914]
  rfl
theorem sub10020 (p : Pattern) : d2857 (change p 225 none) = d5804 p := by
  change (if p 163 then d12 (change p 225 none) else d2856 (change p 225 none)) = d5804 p
  rw [sub9592, sub10019]
  rfl
theorem sub10021 (p : Pattern) : d2858 (change p 225 none) = d5805 p := by
  change (if p 162 then d12 (change p 225 none) else d2857 (change p 225 none)) = d5805 p
  rw [sub9592, sub10020]
  rfl
theorem sub10022 (p : Pattern) : d2859 (change p 225 none) = d5806 p := by
  change (if p 161 then d2858 (change p 225 none) else d2855 (change p 225 none)) = d5806 p
  rw [sub10021, sub10018]
  rfl
theorem sub10023 (p : Pattern) : d2860 (change p 225 none) = d5807 p := by
  change (if p 160 then d2859 (change p 225 none) else d2752 (change p 225 none)) = d5807 p
  rw [sub10022, sub9912]
  rfl
theorem sub10024 (p : Pattern) : d2861 (change p 225 none) = d5808 p := by
  change (if p 182 then d2710 (change p 225 none) else d2692 (change p 225 none)) = d5808 p
  rw [sub9868, sub9840]
  rfl
theorem sub10025 (p : Pattern) : d2862 (change p 225 none) = d5809 p := by
  change (if p 163 then d2714 (change p 225 none) else d2861 (change p 225 none)) = d5809 p
  rw [sub9872, sub10024]
  rfl
theorem sub10026 (p : Pattern) : d2863 (change p 225 none) = d5810 p := by
  change (if p 162 then d2857 (change p 225 none) else d2862 (change p 225 none)) = d5810 p
  rw [sub10020, sub10025]
  rfl
theorem sub10027 (p : Pattern) : d2864 (change p 225 none) = d5811 p := by
  change (if p 162 then d12 (change p 225 none) else d2561 (change p 225 none)) = d5811 p
  rw [sub9592, sub9690]
  rfl
theorem sub10028 (p : Pattern) : d2865 (change p 225 none) = d5812 p := by
  change (if p 161 then d2864 (change p 225 none) else d2863 (change p 225 none)) = d5812 p
  rw [sub10027, sub10026]
  rfl
theorem sub10029 (p : Pattern) : d2866 (change p 225 none) = d5813 p := by
  change (if p 160 then d2865 (change p 225 none) else d2847 (change p 225 none)) = d5813 p
  rw [sub10028, sub10010]
  rfl
theorem sub10030 (p : Pattern) : d2867 (change p 225 none) = d5814 p := by
  change (if p 141 then d2866 (change p 225 none) else d2860 (change p 225 none)) = d5814 p
  rw [sub10029, sub10023]
  rfl
theorem sub10031 (p : Pattern) : d2868 (change p 225 none) = d5815 p := by
  change (if p 163 then d2584 (change p 225 none) else d2753 (change p 225 none)) = d5815 p
  rw [sub9718, sub9913]
  rfl
theorem sub10032 (p : Pattern) : d2869 (change p 225 none) = d5816 p := by
  change (if p 162 then d2868 (change p 225 none) else d2746 (change p 225 none)) = d5816 p
  rw [sub10031, sub9906]
  rfl
theorem sub10033 (p : Pattern) : d2870 (change p 225 none) = d5817 p := by
  change (if p 161 then d2764 (change p 225 none) else d2869 (change p 225 none)) = d5817 p
  rw [sub9924, sub10032]
  rfl
theorem sub10034 (p : Pattern) : d2871 (change p 225 none) = d5818 p := by
  change (if p 160 then d2768 (change p 225 none) else d2870 (change p 225 none)) = d5818 p
  rw [sub9928, sub10033]
  rfl
theorem sub10035 (p : Pattern) : d2872 (change p 225 none) = d5819 p := by
  change (if p 162 then d2844 (change p 225 none) else d2753 (change p 225 none)) = d5819 p
  rw [sub10007, sub9913]
  rfl
theorem sub10036 (p : Pattern) : d2873 (change p 225 none) = d5820 p := by
  change (if p 161 then d2767 (change p 225 none) else d2872 (change p 225 none)) = d5820 p
  rw [sub9927, sub10035]
  rfl
theorem sub10037 (p : Pattern) : d2874 (change p 225 none) = d5821 p := by
  change (if p 162 then d12 (change p 225 none) else d2608 (change p 225 none)) = d5821 p
  rw [sub9592, sub9742]
  rfl
theorem sub10038 (p : Pattern) : d2875 (change p 225 none) = d5822 p := by
  change (if p 161 then d12 (change p 225 none) else d2874 (change p 225 none)) = d5822 p
  rw [sub9592, sub10037]
  rfl
theorem sub10039 (p : Pattern) : d2876 (change p 225 none) = d5823 p := by
  change (if p 160 then d2875 (change p 225 none) else d2873 (change p 225 none)) = d5823 p
  rw [sub10038, sub10036]
  rfl
theorem sub10040 (p : Pattern) : d2877 (change p 225 none) = d5824 p := by
  change (if p 141 then d2876 (change p 225 none) else d2871 (change p 225 none)) = d5824 p
  rw [sub10039, sub10034]
  rfl
theorem sub10041 (p : Pattern) : d2878 (change p 225 none) = d5825 p := by
  change (if p 138 then d2877 (change p 225 none) else d2867 (change p 225 none)) = d5825 p
  rw [sub10040, sub10030]
  rfl
theorem sub10042 (p : Pattern) : d2879 (change p 225 none) = d5826 p := by
  change (if p 163 then d2607 (change p 225 none) else d2753 (change p 225 none)) = d5826 p
  rw [sub9741, sub9913]
  rfl
theorem sub10043 (p : Pattern) : d2880 (change p 225 none) = d5827 p := by
  change (if p 162 then d2879 (change p 225 none) else d2746 (change p 225 none)) = d5827 p
  rw [sub10042, sub9906]
  rfl
theorem sub10044 (p : Pattern) : d2881 (change p 225 none) = d5828 p := by
  change (if p 163 then d2607 (change p 225 none) else d2748 (change p 225 none)) = d5828 p
  rw [sub9741, sub9908]
  rfl
theorem sub10045 (p : Pattern) : d2882 (change p 225 none) = d5829 p := by
  change (if p 162 then d12 (change p 225 none) else d2881 (change p 225 none)) = d5829 p
  rw [sub9592, sub10044]
  rfl
theorem sub10046 (p : Pattern) : d2883 (change p 225 none) = d5830 p := by
  change (if p 161 then d2882 (change p 225 none) else d2880 (change p 225 none)) = d5830 p
  rw [sub10045, sub10043]
  rfl
theorem sub10047 (p : Pattern) : d2884 (change p 225 none) = d5831 p := by
  change (if p 163 then d2584 (change p 225 none) else d2755 (change p 225 none)) = d5831 p
  rw [sub9718, sub9915]
  rfl
theorem sub10048 (p : Pattern) : d2885 (change p 225 none) = d5832 p := by
  change (if p 162 then d12 (change p 225 none) else d2884 (change p 225 none)) = d5832 p
  rw [sub9592, sub10047]
  rfl
theorem sub10049 (p : Pattern) : d2886 (change p 225 none) = d5833 p := by
  change (if p 161 then d12 (change p 225 none) else d2885 (change p 225 none)) = d5833 p
  rw [sub9592, sub10048]
  rfl
theorem sub10050 (p : Pattern) : d2887 (change p 225 none) = d5834 p := by
  change (if p 160 then d2886 (change p 225 none) else d2883 (change p 225 none)) = d5834 p
  rw [sub10049, sub10046]
  rfl
theorem sub10051 (p : Pattern) : d2888 (change p 225 none) = d5835 p := by
  change (if p 141 then d2876 (change p 225 none) else d2887 (change p 225 none)) = d5835 p
  rw [sub10039, sub10050]
  rfl
theorem sub10052 (p : Pattern) : d2889 (change p 225 none) = d5836 p := by
  change (if p 138 then d12 (change p 225 none) else d2888 (change p 225 none)) = d5836 p
  rw [sub9592, sub10051]
  rfl
theorem sub10053 (p : Pattern) : d2890 (change p 225 none) = d5837 p := by
  change (if p 116 then d2889 (change p 225 none) else d2878 (change p 225 none)) = d5837 p
  rw [sub10052, sub10041]
  rfl
theorem sub10054 (p : Pattern) : d2891 (change p 225 none) = d5838 p := by
  change (if p 115 then d2890 (change p 225 none) else d2852 (change p 225 none)) = d5838 p
  rw [sub10053, sub10015]
  rfl
theorem sub10055 (p : Pattern) : d2892 (change p 225 none) = d5839 p := by
  change (if p 71 then d2891 (change p 225 none) else d2652 (change p 225 none)) = d5839 p
  rw [sub10054, sub9786]
  rfl
theorem sub10056 (p : Pattern) : d2893 (change p 225 none) = d5840 p := by
  change (if p 49 then d2892 (change p 225 none) else d2833 (change p 225 none)) = d5840 p
  rw [sub10055, sub9996]
  rfl
theorem sub10057 (p : Pattern) : d2894 (change p 225 none) = d5841 p := by
  change (if p 48 then d2893 (change p 225 none) else d2791 (change p 225 none)) = d5841 p
  rw [sub10056, sub9951]
  rfl
theorem sub10058 (p : Pattern) : d0 (change p 224 none) = d0 p := by
  rfl
theorem sub10059 (p : Pattern) : d12 (change p 224 none) = d12 p := by
  rfl
theorem sub10060 (p : Pattern) : d13 (change p 224 none) = d13 p := by
  change (if p 247 then d12 (change p 224 none) else d0 (change p 224 none)) = d13 p
  rw [sub10059, sub10058]
  rfl
theorem sub10061 (p : Pattern) : d14 (change p 224 none) = d14 p := by
  change (if p 246 then d13 (change p 224 none) else d0 (change p 224 none)) = d14 p
  rw [sub10060, sub10058]
  rfl
theorem sub10062 (p : Pattern) : d2184 (change p 224 none) = d14 p := by
  change d14 (change p 224 none) = d14 p
  exact sub10061 p
theorem sub10063 (p : Pattern) : d2185 (change p 224 none) = d14 p := by
  change d14 (change p 224 none) = d14 p
  exact sub10061 p
theorem sub10064 (p : Pattern) : d2186 (change p 224 none) = d14 p := by
  change (if p 204 then d2185 (change p 224 none) else d2184 (change p 224 none)) = d14 p
  rw [sub10063, sub10062]
  simp only [ite_self]
theorem sub10065 (p : Pattern) : d2187 (change p 224 none) = d15 p := by
  change (if p 204 then d12 (change p 224 none) else d2185 (change p 224 none)) = d15 p
  rw [sub10059, sub10063]
  rfl
theorem sub10066 (p : Pattern) : d2188 (change p 224 none) = d16 p := by
  change (if p 182 then d2187 (change p 224 none) else d2186 (change p 224 none)) = d16 p
  rw [sub10065, sub10064]
  rfl
theorem sub10067 (p : Pattern) : d2189 (change p 224 none) = d14 p := by
  change d14 (change p 224 none) = d14 p
  exact sub10061 p
theorem sub10068 (p : Pattern) : d2190 (change p 224 none) = d14 p := by
  change (if p 204 then d2185 (change p 224 none) else d2189 (change p 224 none)) = d14 p
  rw [sub10063, sub10067]
  simp only [ite_self]
theorem sub10069 (p : Pattern) : d2191 (change p 224 none) = d16 p := by
  change (if p 182 then d2187 (change p 224 none) else d2190 (change p 224 none)) = d16 p
  rw [sub10065, sub10068]
  rfl
theorem sub10070 (p : Pattern) : d2192 (change p 224 none) = d16 p := by
  change (if p 163 then d2191 (change p 224 none) else d2188 (change p 224 none)) = d16 p
  rw [sub10069, sub10066]
  simp only [ite_self]
theorem sub10071 (p : Pattern) : d2193 (change p 224 none) = d14 p := by
  change d14 (change p 224 none) = d14 p
  exact sub10061 p
theorem sub10072 (p : Pattern) : d2194 (change p 224 none) = d14 p := by
  change (if p 204 then d2185 (change p 224 none) else d2193 (change p 224 none)) = d14 p
  rw [sub10063, sub10071]
  simp only [ite_self]
theorem sub10073 (p : Pattern) : d2195 (change p 224 none) = d16 p := by
  change (if p 182 then d2187 (change p 224 none) else d2194 (change p 224 none)) = d16 p
  rw [sub10065, sub10072]
  rfl
theorem sub10074 (p : Pattern) : d4 (change p 224 none) = d4 p := by
  rfl
theorem sub10075 (p : Pattern) : d17 (change p 224 none) = d17 p := by
  change (if p 247 then d12 (change p 224 none) else d4 (change p 224 none)) = d17 p
  rw [sub10059, sub10074]
  rfl
theorem sub10076 (p : Pattern) : d18 (change p 224 none) = d18 p := by
  change (if p 246 then d17 (change p 224 none) else d4 (change p 224 none)) = d18 p
  rw [sub10075, sub10074]
  rfl
theorem sub10077 (p : Pattern) : d2196 (change p 224 none) = d18 p := by
  change d18 (change p 224 none) = d18 p
  exact sub10076 p
theorem sub10078 (p : Pattern) : d2197 (change p 224 none) = d19 p := by
  change (if p 204 then d12 (change p 224 none) else d2196 (change p 224 none)) = d19 p
  rw [sub10059, sub10077]
  rfl
theorem sub10079 (p : Pattern) : d2198 (change p 224 none) = d20 p := by
  change (if p 182 then d2197 (change p 224 none) else d2196 (change p 224 none)) = d20 p
  rw [sub10078, sub10077]
  rfl
end NetHack.Sokoban22Refined85
