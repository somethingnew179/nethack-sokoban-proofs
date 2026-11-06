/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions114
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub13800 (p : Pattern) : d2047 (change p 10000 (some 247)) = d7672 p := by
  change (if p 225 then d1776 (change p 10000 (some 247)) else d1770 (change p 10000 (some 247))) = d7672 p
  rw [sub13709, sub13660]
  rfl
theorem sub13801 (p : Pattern) : d2048 (change p 10000 (some 247)) = d7753 p := by
  change (if p 224 then d2047 (change p 10000 (some 247)) else d1777 (change p 10000 (some 247))) = d7753 p
  rw [sub13800, sub13710]
  rfl
theorem sub13802 (p : Pattern) : d2948 (change p 10000 (some 247)) = d7754 p := by
  change (if p 204 then d2048 (change p 10000 (some 247)) else d14 (change p 10000 (some 247))) = d7754 p
  rw [sub13801, sub13656]
  rfl
theorem sub13803 (p : Pattern) : d1773 (change p 10000 (some 247)) = d7755 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1772 (change p 10000 (some 247))) = d7755 p
  rw [sub13654, sub13662]
  rfl
theorem sub13804 (p : Pattern) : d2949 (change p 10000 (some 247)) = d7756 p := by
  change (if p 182 then d1773 (change p 10000 (some 247)) else d2948 (change p 10000 (some 247))) = d7756 p
  rw [sub13803, sub13802]
  rfl
theorem sub13805 (p : Pattern) : d2051 (change p 10000 (some 247)) = d10 p := by
  change d10 (change p 10000 (some 247)) = d10 p
  exact sub13730 p
theorem sub13806 (p : Pattern) : d2052 (change p 10000 (some 247)) = d3279 p := by
  change (if p 246 then d23 (change p 10000 (some 247)) else d2051 (change p 10000 (some 247))) = d3279 p
  rw [sub13691, sub13805]
  rfl
theorem sub13807 (p : Pattern) : d2053 (change p 10000 (some 247)) = d7706 p := by
  change (if p 225 then d2052 (change p 10000 (some 247)) else d1770 (change p 10000 (some 247))) = d7706 p
  rw [sub13806, sub13660]
  rfl
theorem sub13808 (p : Pattern) : d2054 (change p 10000 (some 247)) = d7757 p := by
  change (if p 224 then d2053 (change p 10000 (some 247)) else d1777 (change p 10000 (some 247))) = d7757 p
  rw [sub13807, sub13710]
  rfl
theorem sub13809 (p : Pattern) : d2950 (change p 10000 (some 247)) = d7758 p := by
  change (if p 204 then d2054 (change p 10000 (some 247)) else d14 (change p 10000 (some 247))) = d7758 p
  rw [sub13808, sub13656]
  rfl
theorem sub13810 (p : Pattern) : d1778 (change p 10000 (some 247)) = d8 p := by
  change d8 (change p 10000 (some 247)) = d8 p
  exact sub13673 p
theorem sub13811 (p : Pattern) : d1779 (change p 10000 (some 247)) = d3461 p := by
  change (if p 246 then d190 (change p 10000 (some 247)) else d1778 (change p 10000 (some 247))) = d3461 p
  rw [sub13675, sub13810]
  rfl
theorem sub13812 (p : Pattern) : d1780 (change p 10000 (some 247)) = d7669 p := by
  change (if p 225 then d1779 (change p 10000 (some 247)) else d1770 (change p 10000 (some 247))) = d7669 p
  rw [sub13811, sub13660]
  rfl
theorem sub13813 (p : Pattern) : d1781 (change p 10000 (some 247)) = d7759 p := by
  change (if p 224 then d1780 (change p 10000 (some 247)) else d1777 (change p 10000 (some 247))) = d7759 p
  rw [sub13812, sub13710]
  rfl
theorem sub13814 (p : Pattern) : d1782 (change p 10000 (some 247)) = d7760 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1781 (change p 10000 (some 247))) = d7760 p
  rw [sub13654, sub13813]
  rfl
theorem sub13815 (p : Pattern) : d2951 (change p 10000 (some 247)) = d7761 p := by
  change (if p 182 then d1782 (change p 10000 (some 247)) else d2950 (change p 10000 (some 247))) = d7761 p
  rw [sub13814, sub13809]
  rfl
theorem sub13816 (p : Pattern) : d2952 (change p 10000 (some 247)) = d7762 p := by
  change (if p 163 then d2951 (change p 10000 (some 247)) else d2949 (change p 10000 (some 247))) = d7762 p
  rw [sub13815, sub13804]
  rfl
theorem sub13817 (p : Pattern) : d1789 (change p 10000 (some 247)) = d7763 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1788 (change p 10000 (some 247))) = d7763 p
  rw [sub13654, sub13714]
  rfl
theorem sub13818 (p : Pattern) : d2953 (change p 10000 (some 247)) = d7764 p := by
  change (if p 182 then d1789 (change p 10000 (some 247)) else d2906 (change p 10000 (some 247))) = d7764 p
  rw [sub13817, sub13715]
  rfl
theorem sub13819 (p : Pattern) : d1798 (change p 10000 (some 247)) = d7765 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1797 (change p 10000 (some 247))) = d7765 p
  rw [sub13654, sub13750]
  rfl
theorem sub13820 (p : Pattern) : d2954 (change p 10000 (some 247)) = d7766 p := by
  change (if p 182 then d1798 (change p 10000 (some 247)) else d2911 (change p 10000 (some 247))) = d7766 p
  rw [sub13819, sub13751]
  rfl
theorem sub13821 (p : Pattern) : d2955 (change p 10000 (some 247)) = d7767 p := by
  change (if p 163 then d2954 (change p 10000 (some 247)) else d2953 (change p 10000 (some 247))) = d7767 p
  rw [sub13820, sub13818]
  rfl
theorem sub13822 (p : Pattern) : d2956 (change p 10000 (some 247)) = d7768 p := by
  change (if p 162 then d2955 (change p 10000 (some 247)) else d2952 (change p 10000 (some 247))) = d7768 p
  rw [sub13821, sub13816]
  rfl
theorem sub13823 (p : Pattern) : d1804 (change p 10000 (some 247)) = d7769 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1803 (change p 10000 (some 247))) = d7769 p
  rw [sub13654, sub13695]
  rfl
theorem sub13824 (p : Pattern) : d2957 (change p 10000 (some 247)) = d7770 p := by
  change (if p 182 then d1804 (change p 10000 (some 247)) else d2901 (change p 10000 (some 247))) = d7770 p
  rw [sub13823, sub13696]
  rfl
theorem sub13825 (p : Pattern) : d2958 (change p 10000 (some 247)) = d7771 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d2957 (change p 10000 (some 247))) = d7771 p
  rw [sub13654, sub13824]
  rfl
theorem sub13826 (p : Pattern) : d2959 (change p 10000 (some 247)) = d7772 p := by
  change (if p 162 then d2958 (change p 10000 (some 247)) else d2955 (change p 10000 (some 247))) = d7772 p
  rw [sub13825, sub13821]
  rfl
theorem sub13827 (p : Pattern) : d2960 (change p 10000 (some 247)) = d7773 p := by
  change (if p 161 then d2959 (change p 10000 (some 247)) else d2956 (change p 10000 (some 247))) = d7773 p
  rw [sub13826, sub13822]
  rfl
theorem sub13828 (p : Pattern) : d2961 (change p 10000 (some 247)) = d7774 p := by
  change (if p 182 then d1718 (change p 10000 (some 247)) else d2935 (change p 10000 (some 247))) = d7774 p
  rw [sub13725, sub13787]
  rfl
theorem sub13829 (p : Pattern) : d2962 (change p 10000 (some 247)) = d7775 p := by
  change (if p 204 then d1724 (change p 10000 (some 247)) else d35 (change p 10000 (some 247))) = d7775 p
  rw [sub13735, sub13727]
  rfl
theorem sub13830 (p : Pattern) : d2963 (change p 10000 (some 247)) = d7776 p := by
  change (if p 182 then d1725 (change p 10000 (some 247)) else d2962 (change p 10000 (some 247))) = d7776 p
  rw [sub13736, sub13829]
  rfl
theorem sub13831 (p : Pattern) : d2964 (change p 10000 (some 247)) = d7777 p := by
  change (if p 163 then d2963 (change p 10000 (some 247)) else d2961 (change p 10000 (some 247))) = d7777 p
  rw [sub13830, sub13828]
  rfl
theorem sub13832 (p : Pattern) : d2965 (change p 10000 (some 247)) = d7778 p := by
  change (if p 162 then d2932 (change p 10000 (some 247)) else d2964 (change p 10000 (some 247))) = d7778 p
  rw [sub13784, sub13831]
  rfl
theorem sub13833 (p : Pattern) : d2966 (change p 10000 (some 247)) = d7779 p := by
  change (if p 161 then d12 (change p 10000 (some 247)) else d2965 (change p 10000 (some 247))) = d7779 p
  rw [sub13654, sub13832]
  rfl
theorem sub13834 (p : Pattern) : d2967 (change p 10000 (some 247)) = d7780 p := by
  change (if p 160 then d2966 (change p 10000 (some 247)) else d2960 (change p 10000 (some 247))) = d7780 p
  rw [sub13833, sub13827]
  rfl
theorem sub13835 (p : Pattern) : d2968 (change p 10000 (some 247)) = d7781 p := by
  change (if p 163 then d2961 (change p 10000 (some 247)) else d2951 (change p 10000 (some 247))) = d7781 p
  rw [sub13828, sub13815]
  rfl
theorem sub13836 (p : Pattern) : d2969 (change p 10000 (some 247)) = d7782 p := by
  change (if p 163 then d2957 (change p 10000 (some 247)) else d2954 (change p 10000 (some 247))) = d7782 p
  rw [sub13824, sub13820]
  rfl
theorem sub13837 (p : Pattern) : d2970 (change p 10000 (some 247)) = d7783 p := by
  change (if p 162 then d2969 (change p 10000 (some 247)) else d2968 (change p 10000 (some 247))) = d7783 p
  rw [sub13836, sub13835]
  rfl
theorem sub13838 (p : Pattern) : d2971 (change p 10000 (some 247)) = d7784 p := by
  change (if p 163 then d2928 (change p 10000 (some 247)) else d2954 (change p 10000 (some 247))) = d7784 p
  rw [sub13780, sub13820]
  rfl
theorem sub13839 (p : Pattern) : d2972 (change p 10000 (some 247)) = d7785 p := by
  change (if p 162 then d2932 (change p 10000 (some 247)) else d2971 (change p 10000 (some 247))) = d7785 p
  rw [sub13784, sub13838]
  rfl
theorem sub13840 (p : Pattern) : d2973 (change p 10000 (some 247)) = d7786 p := by
  change (if p 161 then d2972 (change p 10000 (some 247)) else d2970 (change p 10000 (some 247))) = d7786 p
  rw [sub13839, sub13837]
  rfl
theorem sub13841 (p : Pattern) : d2974 (change p 10000 (some 247)) = d7787 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d2963 (change p 10000 (some 247))) = d7787 p
  rw [sub13654, sub13830]
  rfl
theorem sub13842 (p : Pattern) : d2975 (change p 10000 (some 247)) = d7788 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d2974 (change p 10000 (some 247))) = d7788 p
  rw [sub13654, sub13841]
  rfl
theorem sub13843 (p : Pattern) : d2976 (change p 10000 (some 247)) = d7789 p := by
  change (if p 161 then d12 (change p 10000 (some 247)) else d2975 (change p 10000 (some 247))) = d7789 p
  rw [sub13654, sub13842]
  rfl
theorem sub13844 (p : Pattern) : d2977 (change p 10000 (some 247)) = d7790 p := by
  change (if p 160 then d2976 (change p 10000 (some 247)) else d2973 (change p 10000 (some 247))) = d7790 p
  rw [sub13843, sub13840]
  rfl
theorem sub13845 (p : Pattern) : d2978 (change p 10000 (some 247)) = d7791 p := by
  change (if p 141 then d2977 (change p 10000 (some 247)) else d2967 (change p 10000 (some 247))) = d7791 p
  rw [sub13844, sub13834]
  rfl
theorem sub13846 (p : Pattern) : d2979 (change p 10000 (some 247)) = d7792 p := by
  change (if p 138 then d2978 (change p 10000 (some 247)) else d2947 (change p 10000 (some 247))) = d7792 p
  rw [sub13845, sub13799]
  rfl
theorem sub13847 (p : Pattern) : d2980 (change p 10000 (some 247)) = d7793 p := by
  change (if p 163 then d2931 (change p 10000 (some 247)) else d2957 (change p 10000 (some 247))) = d7793 p
  rw [sub13783, sub13824]
  rfl
theorem sub13848 (p : Pattern) : d2981 (change p 10000 (some 247)) = d7794 p := by
  change (if p 162 then d2932 (change p 10000 (some 247)) else d2980 (change p 10000 (some 247))) = d7794 p
  rw [sub13784, sub13847]
  rfl
theorem sub13849 (p : Pattern) : d2982 (change p 10000 (some 247)) = d7795 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d2932 (change p 10000 (some 247))) = d7795 p
  rw [sub13654, sub13784]
  rfl
theorem sub13850 (p : Pattern) : d2983 (change p 10000 (some 247)) = d7796 p := by
  change (if p 161 then d2982 (change p 10000 (some 247)) else d2981 (change p 10000 (some 247))) = d7796 p
  rw [sub13849, sub13848]
  rfl
theorem sub13851 (p : Pattern) : d2984 (change p 10000 (some 247)) = d7797 p := by
  change (if p 161 then d12 (change p 10000 (some 247)) else d2982 (change p 10000 (some 247))) = d7797 p
  rw [sub13654, sub13849]
  rfl
theorem sub13852 (p : Pattern) : d2985 (change p 10000 (some 247)) = d7798 p := by
  change (if p 160 then d2984 (change p 10000 (some 247)) else d2983 (change p 10000 (some 247))) = d7798 p
  rw [sub13851, sub13850]
  rfl
theorem sub13853 (p : Pattern) : d2986 (change p 10000 (some 247)) = d7799 p := by
  change (if p 160 then d12 (change p 10000 (some 247)) else d2984 (change p 10000 (some 247))) = d7799 p
  rw [sub13654, sub13851]
  rfl
theorem sub13854 (p : Pattern) : d2987 (change p 10000 (some 247)) = d7800 p := by
  change (if p 141 then d2986 (change p 10000 (some 247)) else d2985 (change p 10000 (some 247))) = d7800 p
  rw [sub13853, sub13852]
  rfl
theorem sub13855 (p : Pattern) : d2988 (change p 10000 (some 247)) = d7801 p := by
  change (if p 138 then d2987 (change p 10000 (some 247)) else d2978 (change p 10000 (some 247))) = d7801 p
  rw [sub13854, sub13845]
  rfl
theorem sub13856 (p : Pattern) : d2989 (change p 10000 (some 247)) = d7802 p := by
  change (if p 116 then d2988 (change p 10000 (some 247)) else d2979 (change p 10000 (some 247))) = d7802 p
  rw [sub13855, sub13846]
  rfl
theorem sub13857 (p : Pattern) : d2990 (change p 10000 (some 247)) = d7803 p := by
  change (if p 138 then d12 (change p 10000 (some 247)) else d2978 (change p 10000 (some 247))) = d7803 p
  rw [sub13654, sub13845]
  rfl
theorem sub13858 (p : Pattern) : d2991 (change p 10000 (some 247)) = d7804 p := by
  change (if p 116 then d2990 (change p 10000 (some 247)) else d2979 (change p 10000 (some 247))) = d7804 p
  rw [sub13857, sub13846]
  rfl
theorem sub13859 (p : Pattern) : d2992 (change p 10000 (some 247)) = d7805 p := by
  change (if p 115 then d2991 (change p 10000 (some 247)) else d2989 (change p 10000 (some 247))) = d7805 p
  rw [sub13858, sub13856]
  rfl
theorem sub13860 (p : Pattern) : d1 (change p 10000 (some 247)) = d1 p := by
  rfl
theorem sub13861 (p : Pattern) : d102 (change p 10000 (some 247)) = d12 p := by
  change d12 (change p 10000 (some 247)) = d12 p
  exact sub13654 p
theorem sub13862 (p : Pattern) : d103 (change p 10000 (some 247)) = d3358 p := by
  change (if p 246 then d102 (change p 10000 (some 247)) else d1 (change p 10000 (some 247))) = d3358 p
  rw [sub13861, sub13860]
  rfl
theorem sub13863 (p : Pattern) : d5 (change p 10000 (some 247)) = d5 p := by
  rfl
theorem sub13864 (p : Pattern) : d1939 (change p 10000 (some 247)) = d5 p := by
  change d5 (change p 10000 (some 247)) = d5 p
  exact sub13863 p
theorem sub13865 (p : Pattern) : d106 (change p 10000 (some 247)) = d12 p := by
  change d12 (change p 10000 (some 247)) = d12 p
  exact sub13654 p
theorem sub13866 (p : Pattern) : d1940 (change p 10000 (some 247)) = d3366 p := by
  change (if p 246 then d106 (change p 10000 (some 247)) else d1939 (change p 10000 (some 247))) = d3366 p
  rw [sub13865, sub13864]
  rfl
theorem sub13867 (p : Pattern) : d1941 (change p 10000 (some 247)) = d7806 p := by
  change (if p 225 then d1940 (change p 10000 (some 247)) else d103 (change p 10000 (some 247))) = d7806 p
  rw [sub13866, sub13862]
  rfl
theorem sub13868 (p : Pattern) : d1942 (change p 10000 (some 247)) = d7807 p := by
  change (if p 224 then d1940 (change p 10000 (some 247)) else d1941 (change p 10000 (some 247))) = d7807 p
  rw [sub13866, sub13867]
  rfl
theorem sub13869 (p : Pattern) : d2993 (change p 10000 (some 247)) = d7808 p := by
  change (if p 204 then d1942 (change p 10000 (some 247)) else d103 (change p 10000 (some 247))) = d7808 p
  rw [sub13868, sub13862]
  rfl
theorem sub13870 (p : Pattern) : d3 (change p 10000 (some 247)) = d3 p := by
  rfl
theorem sub13871 (p : Pattern) : d1872 (change p 10000 (some 247)) = d3 p := by
  change d3 (change p 10000 (some 247)) = d3 p
  exact sub13870 p
theorem sub13872 (p : Pattern) : d115 (change p 10000 (some 247)) = d12 p := by
  change d12 (change p 10000 (some 247)) = d12 p
  exact sub13654 p
theorem sub13873 (p : Pattern) : d1873 (change p 10000 (some 247)) = d3374 p := by
  change (if p 246 then d115 (change p 10000 (some 247)) else d1872 (change p 10000 (some 247))) = d3374 p
  rw [sub13872, sub13871]
  rfl
theorem sub13874 (p : Pattern) : d1874 (change p 10000 (some 247)) = d7809 p := by
  change (if p 225 then d1873 (change p 10000 (some 247)) else d103 (change p 10000 (some 247))) = d7809 p
  rw [sub13873, sub13862]
  rfl
theorem sub13875 (p : Pattern) : d1875 (change p 10000 (some 247)) = d7810 p := by
  change (if p 224 then d1873 (change p 10000 (some 247)) else d1874 (change p 10000 (some 247))) = d7810 p
  rw [sub13873, sub13874]
  rfl
theorem sub13876 (p : Pattern) : d1876 (change p 10000 (some 247)) = d7811 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1875 (change p 10000 (some 247))) = d7811 p
  rw [sub13654, sub13875]
  rfl
theorem sub13877 (p : Pattern) : d2994 (change p 10000 (some 247)) = d7812 p := by
  change (if p 182 then d1876 (change p 10000 (some 247)) else d2993 (change p 10000 (some 247))) = d7812 p
  rw [sub13876, sub13869]
  rfl
theorem sub13878 (p : Pattern) : d107 (change p 10000 (some 247)) = d3366 p := by
  change (if p 246 then d106 (change p 10000 (some 247)) else d5 (change p 10000 (some 247))) = d3366 p
  rw [sub13865, sub13863]
  rfl
theorem sub13879 (p : Pattern) : d1963 (change p 10000 (some 247)) = d9 p := by
  change d9 (change p 10000 (some 247)) = d9 p
  exact sub13690 p
theorem sub13880 (p : Pattern) : d1964 (change p 10000 (some 247)) = d3244 p := by
  change (if p 246 then d23 (change p 10000 (some 247)) else d1963 (change p 10000 (some 247))) = d3244 p
  rw [sub13691, sub13879]
  rfl
theorem sub13881 (p : Pattern) : d2129 (change p 10000 (some 247)) = d7813 p := by
  change (if p 225 then d1964 (change p 10000 (some 247)) else d107 (change p 10000 (some 247))) = d7813 p
  rw [sub13880, sub13878]
  rfl
theorem sub13882 (p : Pattern) : d2130 (change p 10000 (some 247)) = d7814 p := by
  change (if p 224 then d1964 (change p 10000 (some 247)) else d2129 (change p 10000 (some 247))) = d7814 p
  rw [sub13880, sub13881]
  rfl
theorem sub13883 (p : Pattern) : d2995 (change p 10000 (some 247)) = d7815 p := by
  change (if p 204 then d2130 (change p 10000 (some 247)) else d107 (change p 10000 (some 247))) = d7815 p
  rw [sub13882, sub13878]
  rfl
theorem sub13884 (p : Pattern) : d7 (change p 10000 (some 247)) = d7 p := by
  rfl
theorem sub13885 (p : Pattern) : d1880 (change p 10000 (some 247)) = d7 p := by
  change d7 (change p 10000 (some 247)) = d7 p
  exact sub13884 p
theorem sub13886 (p : Pattern) : d119 (change p 10000 (some 247)) = d12 p := by
  change d12 (change p 10000 (some 247)) = d12 p
  exact sub13654 p
theorem sub13887 (p : Pattern) : d1881 (change p 10000 (some 247)) = d3377 p := by
  change (if p 246 then d119 (change p 10000 (some 247)) else d1880 (change p 10000 (some 247))) = d3377 p
  rw [sub13886, sub13885]
  rfl
theorem sub13888 (p : Pattern) : d1882 (change p 10000 (some 247)) = d7816 p := by
  change (if p 225 then d1881 (change p 10000 (some 247)) else d107 (change p 10000 (some 247))) = d7816 p
  rw [sub13887, sub13878]
  rfl
theorem sub13889 (p : Pattern) : d1883 (change p 10000 (some 247)) = d7817 p := by
  change (if p 224 then d1881 (change p 10000 (some 247)) else d1882 (change p 10000 (some 247))) = d7817 p
  rw [sub13887, sub13888]
  rfl
theorem sub13890 (p : Pattern) : d1884 (change p 10000 (some 247)) = d7818 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1883 (change p 10000 (some 247))) = d7818 p
  rw [sub13654, sub13889]
  rfl
theorem sub13891 (p : Pattern) : d2996 (change p 10000 (some 247)) = d7819 p := by
  change (if p 182 then d1884 (change p 10000 (some 247)) else d2995 (change p 10000 (some 247))) = d7819 p
  rw [sub13890, sub13883]
  rfl
theorem sub13892 (p : Pattern) : d2997 (change p 10000 (some 247)) = d7820 p := by
  change (if p 163 then d2996 (change p 10000 (some 247)) else d2994 (change p 10000 (some 247))) = d7820 p
  rw [sub13891, sub13877]
  rfl
theorem sub13893 (p : Pattern) : d2998 (change p 10000 (some 247)) = d7821 p := by
  change (if p 162 then d2997 (change p 10000 (some 247)) else d2994 (change p 10000 (some 247))) = d7821 p
  rw [sub13892, sub13877]
  rfl
theorem sub13894 (p : Pattern) : d2999 (change p 10000 (some 247)) = d7822 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d2928 (change p 10000 (some 247))) = d7822 p
  rw [sub13654, sub13780]
  rfl
theorem sub13895 (p : Pattern) : d3000 (change p 10000 (some 247)) = d7823 p := by
  change (if p 162 then d2999 (change p 10000 (some 247)) else d2997 (change p 10000 (some 247))) = d7823 p
  rw [sub13894, sub13892]
  rfl
theorem sub13896 (p : Pattern) : d3001 (change p 10000 (some 247)) = d7824 p := by
  change (if p 161 then d3000 (change p 10000 (some 247)) else d2998 (change p 10000 (some 247))) = d7824 p
  rw [sub13895, sub13893]
  rfl
theorem sub13897 (p : Pattern) : d1945 (change p 10000 (some 247)) = d7 p := by
  change d7 (change p 10000 (some 247)) = d7 p
  exact sub13884 p
theorem sub13898 (p : Pattern) : d1946 (change p 10000 (some 247)) = d3377 p := by
  change (if p 246 then d119 (change p 10000 (some 247)) else d1945 (change p 10000 (some 247))) = d3377 p
  rw [sub13886, sub13897]
  rfl
theorem sub13899 (p : Pattern) : d1947 (change p 10000 (some 247)) = d7825 p := by
  change (if p 225 then d1946 (change p 10000 (some 247)) else d103 (change p 10000 (some 247))) = d7825 p
  rw [sub13898, sub13862]
  rfl
theorem sub13900 (p : Pattern) : d1955 (change p 10000 (some 247)) = d12 p := by
  change (if p 246 then d57 (change p 10000 (some 247)) else d102 (change p 10000 (some 247))) = d12 p
  rw [sub13732, sub13861]
  simp only [ite_self]
theorem sub13901 (p : Pattern) : d1956 (change p 10000 (some 247)) = d7826 p := by
  change (if p 225 then d1955 (change p 10000 (some 247)) else d1940 (change p 10000 (some 247))) = d7826 p
  rw [sub13900, sub13866]
  rfl
theorem sub13902 (p : Pattern) : d1957 (change p 10000 (some 247)) = d7827 p := by
  change (if p 224 then d1956 (change p 10000 (some 247)) else d1947 (change p 10000 (some 247))) = d7827 p
  rw [sub13901, sub13899]
  rfl
theorem sub13903 (p : Pattern) : d3002 (change p 10000 (some 247)) = d7828 p := by
  change (if p 204 then d1957 (change p 10000 (some 247)) else d103 (change p 10000 (some 247))) = d7828 p
  rw [sub13902, sub13862]
  rfl
theorem sub13904 (p : Pattern) : d116 (change p 10000 (some 247)) = d3374 p := by
  change (if p 246 then d115 (change p 10000 (some 247)) else d3 (change p 10000 (some 247))) = d3374 p
  rw [sub13872, sub13870]
  rfl
theorem sub13905 (p : Pattern) : d1891 (change p 10000 (some 247)) = d9 p := by
  change d9 (change p 10000 (some 247)) = d9 p
  exact sub13690 p
theorem sub13906 (p : Pattern) : d1892 (change p 10000 (some 247)) = d3244 p := by
  change (if p 246 then d23 (change p 10000 (some 247)) else d1891 (change p 10000 (some 247))) = d3244 p
  rw [sub13691, sub13905]
  rfl
theorem sub13907 (p : Pattern) : d1893 (change p 10000 (some 247)) = d7829 p := by
  change (if p 225 then d1892 (change p 10000 (some 247)) else d116 (change p 10000 (some 247))) = d7829 p
  rw [sub13906, sub13904]
  rfl
theorem sub13908 (p : Pattern) : d1894 (change p 10000 (some 247)) = d7 p := by
  change d7 (change p 10000 (some 247)) = d7 p
  exact sub13884 p
theorem sub13909 (p : Pattern) : d1895 (change p 10000 (some 247)) = d3377 p := by
  change (if p 246 then d119 (change p 10000 (some 247)) else d1894 (change p 10000 (some 247))) = d3377 p
  rw [sub13886, sub13908]
  rfl
theorem sub13910 (p : Pattern) : d1896 (change p 10000 (some 247)) = d12 p := by
  change (if p 246 then d12 (change p 10000 (some 247)) else d115 (change p 10000 (some 247))) = d12 p
  rw [sub13654, sub13872]
  simp only [ite_self]
theorem sub13911 (p : Pattern) : d1897 (change p 10000 (some 247)) = d7830 p := by
  change (if p 225 then d1896 (change p 10000 (some 247)) else d1895 (change p 10000 (some 247))) = d7830 p
  rw [sub13910, sub13909]
  rfl
theorem sub13912 (p : Pattern) : d1898 (change p 10000 (some 247)) = d7831 p := by
  change (if p 224 then d1897 (change p 10000 (some 247)) else d1893 (change p 10000 (some 247))) = d7831 p
  rw [sub13911, sub13907]
  rfl
theorem sub13913 (p : Pattern) : d1899 (change p 10000 (some 247)) = d7832 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1898 (change p 10000 (some 247))) = d7832 p
  rw [sub13654, sub13912]
  rfl
theorem sub13914 (p : Pattern) : d3003 (change p 10000 (some 247)) = d7833 p := by
  change (if p 182 then d1899 (change p 10000 (some 247)) else d3002 (change p 10000 (some 247))) = d7833 p
  rw [sub13913, sub13903]
  rfl
theorem sub13915 (p : Pattern) : d120 (change p 10000 (some 247)) = d3377 p := by
  change (if p 246 then d119 (change p 10000 (some 247)) else d7 (change p 10000 (some 247))) = d3377 p
  rw [sub13886, sub13884]
  rfl
theorem sub13916 (p : Pattern) : d317 (change p 10000 (some 247)) = d12 p := by
  change (if p 246 then d12 (change p 10000 (some 247)) else d119 (change p 10000 (some 247))) = d12 p
  rw [sub13654, sub13886]
  simp only [ite_self]
theorem sub13917 (p : Pattern) : d1901 (change p 10000 (some 247)) = d7830 p := by
  change (if p 225 then d317 (change p 10000 (some 247)) else d120 (change p 10000 (some 247))) = d7830 p
  rw [sub13916, sub13915]
  rfl
theorem sub13918 (p : Pattern) : d1902 (change p 10000 (some 247)) = d11 p := by
  change d11 (change p 10000 (some 247)) = d11 p
  exact sub13697 p
theorem sub13919 (p : Pattern) : d1903 (change p 10000 (some 247)) = d3257 p := by
  change (if p 246 then d39 (change p 10000 (some 247)) else d1902 (change p 10000 (some 247))) = d3257 p
  rw [sub13699, sub13918]
  rfl
end NetHack.Sokoban22Refined85
