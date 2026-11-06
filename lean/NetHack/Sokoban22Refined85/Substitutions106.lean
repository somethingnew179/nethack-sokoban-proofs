/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions105
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub12720 (p : Pattern) : d2934 (change p 10000 (some 204)) = d7038 p := by
  change (if p 161 then d2933 (change p 10000 (some 204)) else d2926 (change p 10000 (some 204))) = d7038 p
  rw [sub12719, sub12702]
  rfl
theorem sub12721 (p : Pattern) : d1710 (change p 10000 (some 204)) = d1710 p := by
  change (if p 247 then d8 (change p 10000 (some 204)) else d2 (change p 10000 (some 204))) = d1710 p
  rw [sub12630, sub12690]
  rfl
theorem sub12722 (p : Pattern) : d1711 (change p 10000 (some 204)) = d1711 p := by
  change (if p 246 then d190 (change p 10000 (some 204)) else d1710 (change p 10000 (some 204))) = d1711 p
  rw [sub12632, sub12721]
  rfl
theorem sub12723 (p : Pattern) : d1712 (change p 10000 (some 204)) = d1712 p := by
  change (if p 225 then d1711 (change p 10000 (some 204)) else d31 (change p 10000 (some 204))) = d1712 p
  rw [sub12722, sub12692]
  rfl
theorem sub12724 (p : Pattern) : d1715 (change p 10000 (some 204)) = d1715 p := by
  change (if p 246 then d39 (change p 10000 (some 204)) else d30 (change p 10000 (some 204))) = d1715 p
  rw [sub12711, sub12691]
  rfl
theorem sub12725 (p : Pattern) : d1716 (change p 10000 (some 204)) = d1716 p := by
  change (if p 225 then d1715 (change p 10000 (some 204)) else d1714 (change p 10000 (some 204))) = d1716 p
  rw [sub12724, sub12694]
  rfl
theorem sub12726 (p : Pattern) : d1717 (change p 10000 (some 204)) = d1717 p := by
  change (if p 224 then d1716 (change p 10000 (some 204)) else d1712 (change p 10000 (some 204))) = d1717 p
  rw [sub12725, sub12723]
  rfl
theorem sub12727 (p : Pattern) : d2935 (change p 10000 (some 204)) = d1717 p := by
  change d1717 (change p 10000 (some 204)) = d1717 p
  exact sub12726 p
theorem sub12728 (p : Pattern) : d2936 (change p 10000 (some 204)) = d7039 p := by
  change (if p 182 then d12 (change p 10000 (some 204)) else d2935 (change p 10000 (some 204))) = d7039 p
  rw [sub12617, sub12727]
  rfl
theorem sub12729 (p : Pattern) : d2937 (change p 10000 (some 204)) = d7040 p := by
  change (if p 163 then d2936 (change p 10000 (some 204)) else d2908 (change p 10000 (some 204))) = d7040 p
  rw [sub12728, sub12667]
  rfl
theorem sub12730 (p : Pattern) : d2938 (change p 10000 (some 204)) = d7041 p := by
  change (if p 163 then d2917 (change p 10000 (some 204)) else d2912 (change p 10000 (some 204))) = d7041 p
  rw [sub12685, sub12680]
  rfl
theorem sub12731 (p : Pattern) : d2939 (change p 10000 (some 204)) = d7042 p := by
  change (if p 162 then d2938 (change p 10000 (some 204)) else d2937 (change p 10000 (some 204))) = d7042 p
  rw [sub12730, sub12729]
  rfl
theorem sub12732 (p : Pattern) : d2940 (change p 10000 (some 204)) = d7033 p := by
  change (if p 182 then d12 (change p 10000 (some 204)) else d2927 (change p 10000 (some 204))) = d7033 p
  rw [sub12617, sub12707]
  rfl
theorem sub12733 (p : Pattern) : d2941 (change p 10000 (some 204)) = d7043 p := by
  change (if p 163 then d2940 (change p 10000 (some 204)) else d2912 (change p 10000 (some 204))) = d7043 p
  rw [sub12732, sub12680]
  rfl
theorem sub12734 (p : Pattern) : d2942 (change p 10000 (some 204)) = d7035 p := by
  change (if p 182 then d12 (change p 10000 (some 204)) else d2930 (change p 10000 (some 204))) = d7035 p
  rw [sub12617, sub12716]
  rfl
theorem sub12735 (p : Pattern) : d2943 (change p 10000 (some 204)) = d7036 p := by
  change (if p 163 then d12 (change p 10000 (some 204)) else d2942 (change p 10000 (some 204))) = d7036 p
  rw [sub12617, sub12734]
  rfl
theorem sub12736 (p : Pattern) : d2944 (change p 10000 (some 204)) = d7044 p := by
  change (if p 162 then d2943 (change p 10000 (some 204)) else d2941 (change p 10000 (some 204))) = d7044 p
  rw [sub12735, sub12733]
  rfl
theorem sub12737 (p : Pattern) : d2945 (change p 10000 (some 204)) = d7045 p := by
  change (if p 161 then d2944 (change p 10000 (some 204)) else d2939 (change p 10000 (some 204))) = d7045 p
  rw [sub12736, sub12731]
  rfl
theorem sub12738 (p : Pattern) : d2946 (change p 10000 (some 204)) = d7046 p := by
  change (if p 160 then d2945 (change p 10000 (some 204)) else d2934 (change p 10000 (some 204))) = d7046 p
  rw [sub12737, sub12720]
  rfl
theorem sub12739 (p : Pattern) : d2947 (change p 10000 (some 204)) = d7047 p := by
  change (if p 141 then d2946 (change p 10000 (some 204)) else d2921 (change p 10000 (some 204))) = d7047 p
  rw [sub12738, sub12689]
  rfl
theorem sub12740 (p : Pattern) : d2047 (change p 10000 (some 204)) = d2047 p := by
  change (if p 225 then d1776 (change p 10000 (some 204)) else d1770 (change p 10000 (some 204))) = d2047 p
  rw [sub12656, sub12623]
  rfl
theorem sub12741 (p : Pattern) : d2048 (change p 10000 (some 204)) = d2048 p := by
  change (if p 224 then d2047 (change p 10000 (some 204)) else d1777 (change p 10000 (some 204))) = d2048 p
  rw [sub12740, sub12657]
  rfl
theorem sub12742 (p : Pattern) : d2948 (change p 10000 (some 204)) = d2048 p := by
  change d2048 (change p 10000 (some 204)) = d2048 p
  exact sub12741 p
theorem sub12743 (p : Pattern) : d1773 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12744 (p : Pattern) : d2949 (change p 10000 (some 204)) = d7048 p := by
  change (if p 182 then d1773 (change p 10000 (some 204)) else d2948 (change p 10000 (some 204))) = d7048 p
  rw [sub12743, sub12742]
  rfl
theorem sub12745 (p : Pattern) : d2051 (change p 10000 (some 204)) = d2051 p := by
  change (if p 247 then d10 (change p 10000 (some 204)) else d0 (change p 10000 (some 204))) = d2051 p
  rw [sub12671, sub12616]
  rfl
theorem sub12746 (p : Pattern) : d2052 (change p 10000 (some 204)) = d2052 p := by
  change (if p 246 then d23 (change p 10000 (some 204)) else d2051 (change p 10000 (some 204))) = d2052 p
  rw [sub12642, sub12745]
  rfl
theorem sub12747 (p : Pattern) : d2053 (change p 10000 (some 204)) = d2053 p := by
  change (if p 225 then d2052 (change p 10000 (some 204)) else d1770 (change p 10000 (some 204))) = d2053 p
  rw [sub12746, sub12623]
  rfl
theorem sub12748 (p : Pattern) : d2054 (change p 10000 (some 204)) = d2054 p := by
  change (if p 224 then d2053 (change p 10000 (some 204)) else d1777 (change p 10000 (some 204))) = d2054 p
  rw [sub12747, sub12657]
  rfl
theorem sub12749 (p : Pattern) : d2950 (change p 10000 (some 204)) = d2054 p := by
  change d2054 (change p 10000 (some 204)) = d2054 p
  exact sub12748 p
theorem sub12750 (p : Pattern) : d1782 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12751 (p : Pattern) : d2951 (change p 10000 (some 204)) = d7049 p := by
  change (if p 182 then d1782 (change p 10000 (some 204)) else d2950 (change p 10000 (some 204))) = d7049 p
  rw [sub12750, sub12749]
  rfl
theorem sub12752 (p : Pattern) : d2952 (change p 10000 (some 204)) = d7050 p := by
  change (if p 163 then d2951 (change p 10000 (some 204)) else d2949 (change p 10000 (some 204))) = d7050 p
  rw [sub12751, sub12744]
  rfl
theorem sub12753 (p : Pattern) : d1789 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12754 (p : Pattern) : d2953 (change p 10000 (some 204)) = d7022 p := by
  change (if p 182 then d1789 (change p 10000 (some 204)) else d2906 (change p 10000 (some 204))) = d7022 p
  rw [sub12753, sub12663]
  rfl
theorem sub12755 (p : Pattern) : d1798 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12756 (p : Pattern) : d2954 (change p 10000 (some 204)) = d7023 p := by
  change (if p 182 then d1798 (change p 10000 (some 204)) else d2911 (change p 10000 (some 204))) = d7023 p
  rw [sub12755, sub12679]
  rfl
theorem sub12757 (p : Pattern) : d2955 (change p 10000 (some 204)) = d7024 p := by
  change (if p 163 then d2954 (change p 10000 (some 204)) else d2953 (change p 10000 (some 204))) = d7024 p
  rw [sub12756, sub12754]
  rfl
theorem sub12758 (p : Pattern) : d2956 (change p 10000 (some 204)) = d7051 p := by
  change (if p 162 then d2955 (change p 10000 (some 204)) else d2952 (change p 10000 (some 204))) = d7051 p
  rw [sub12757, sub12752]
  rfl
theorem sub12759 (p : Pattern) : d1804 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12760 (p : Pattern) : d2957 (change p 10000 (some 204)) = d7018 p := by
  change (if p 182 then d1804 (change p 10000 (some 204)) else d2901 (change p 10000 (some 204))) = d7018 p
  rw [sub12759, sub12647]
  rfl
theorem sub12761 (p : Pattern) : d2958 (change p 10000 (some 204)) = d7019 p := by
  change (if p 163 then d12 (change p 10000 (some 204)) else d2957 (change p 10000 (some 204))) = d7019 p
  rw [sub12617, sub12760]
  rfl
theorem sub12762 (p : Pattern) : d2959 (change p 10000 (some 204)) = d7026 p := by
  change (if p 162 then d2958 (change p 10000 (some 204)) else d2955 (change p 10000 (some 204))) = d7026 p
  rw [sub12761, sub12757]
  rfl
theorem sub12763 (p : Pattern) : d2960 (change p 10000 (some 204)) = d7052 p := by
  change (if p 161 then d2959 (change p 10000 (some 204)) else d2956 (change p 10000 (some 204))) = d7052 p
  rw [sub12762, sub12758]
  rfl
theorem sub12764 (p : Pattern) : d2961 (change p 10000 (some 204)) = d7039 p := by
  change (if p 182 then d1718 (change p 10000 (some 204)) else d2935 (change p 10000 (some 204))) = d7039 p
  rw [sub12664, sub12727]
  rfl
theorem sub12765 (p : Pattern) : d35 (change p 10000 (some 204)) = d35 p := by
  change (if p 246 then d34 (change p 10000 (some 204)) else d6 (change p 10000 (some 204))) = d35 p
  rw [sub12655, sub12653]
  rfl
theorem sub12766 (p : Pattern) : d364 (change p 10000 (some 204)) = d364 p := by
  change (if p 246 then d12 (change p 10000 (some 204)) else d34 (change p 10000 (some 204))) = d364 p
  rw [sub12617, sub12655]
  rfl
theorem sub12767 (p : Pattern) : d1720 (change p 10000 (some 204)) = d1720 p := by
  change (if p 225 then d364 (change p 10000 (some 204)) else d35 (change p 10000 (some 204))) = d1720 p
  rw [sub12766, sub12765]
  rfl
theorem sub12768 (p : Pattern) : d1721 (change p 10000 (some 204)) = d1721 p := by
  change (if p 247 then d10 (change p 10000 (some 204)) else d6 (change p 10000 (some 204))) = d1721 p
  rw [sub12671, sub12653]
  rfl
theorem sub12769 (p : Pattern) : d1722 (change p 10000 (some 204)) = d1722 p := by
  change (if p 246 then d57 (change p 10000 (some 204)) else d1721 (change p 10000 (some 204))) = d1722 p
  rw [sub12673, sub12768]
  rfl
theorem sub12770 (p : Pattern) : d1723 (change p 10000 (some 204)) = d1723 p := by
  change (if p 225 then d364 (change p 10000 (some 204)) else d1722 (change p 10000 (some 204))) = d1723 p
  rw [sub12766, sub12769]
  rfl
theorem sub12771 (p : Pattern) : d1724 (change p 10000 (some 204)) = d1724 p := by
  change (if p 224 then d1723 (change p 10000 (some 204)) else d1720 (change p 10000 (some 204))) = d1724 p
  rw [sub12770, sub12767]
  rfl
theorem sub12772 (p : Pattern) : d2962 (change p 10000 (some 204)) = d1724 p := by
  change d1724 (change p 10000 (some 204)) = d1724 p
  exact sub12771 p
theorem sub12773 (p : Pattern) : d2963 (change p 10000 (some 204)) = d7053 p := by
  change (if p 182 then d1725 (change p 10000 (some 204)) else d2962 (change p 10000 (some 204))) = d7053 p
  rw [sub12666, sub12772]
  rfl
theorem sub12774 (p : Pattern) : d2964 (change p 10000 (some 204)) = d7054 p := by
  change (if p 163 then d2963 (change p 10000 (some 204)) else d2961 (change p 10000 (some 204))) = d7054 p
  rw [sub12773, sub12764]
  rfl
theorem sub12775 (p : Pattern) : d2965 (change p 10000 (some 204)) = d7055 p := by
  change (if p 162 then d2932 (change p 10000 (some 204)) else d2964 (change p 10000 (some 204))) = d7055 p
  rw [sub12718, sub12774]
  rfl
theorem sub12776 (p : Pattern) : d2966 (change p 10000 (some 204)) = d7056 p := by
  change (if p 161 then d12 (change p 10000 (some 204)) else d2965 (change p 10000 (some 204))) = d7056 p
  rw [sub12617, sub12775]
  rfl
theorem sub12777 (p : Pattern) : d2967 (change p 10000 (some 204)) = d7057 p := by
  change (if p 160 then d2966 (change p 10000 (some 204)) else d2960 (change p 10000 (some 204))) = d7057 p
  rw [sub12776, sub12763]
  rfl
theorem sub12778 (p : Pattern) : d2968 (change p 10000 (some 204)) = d7058 p := by
  change (if p 163 then d2961 (change p 10000 (some 204)) else d2951 (change p 10000 (some 204))) = d7058 p
  rw [sub12764, sub12751]
  rfl
theorem sub12779 (p : Pattern) : d2969 (change p 10000 (some 204)) = d7041 p := by
  change (if p 163 then d2957 (change p 10000 (some 204)) else d2954 (change p 10000 (some 204))) = d7041 p
  rw [sub12760, sub12756]
  rfl
theorem sub12780 (p : Pattern) : d2970 (change p 10000 (some 204)) = d7059 p := by
  change (if p 162 then d2969 (change p 10000 (some 204)) else d2968 (change p 10000 (some 204))) = d7059 p
  rw [sub12779, sub12778]
  rfl
theorem sub12781 (p : Pattern) : d2971 (change p 10000 (some 204)) = d7043 p := by
  change (if p 163 then d2928 (change p 10000 (some 204)) else d2954 (change p 10000 (some 204))) = d7043 p
  rw [sub12709, sub12756]
  rfl
theorem sub12782 (p : Pattern) : d2972 (change p 10000 (some 204)) = d7044 p := by
  change (if p 162 then d2932 (change p 10000 (some 204)) else d2971 (change p 10000 (some 204))) = d7044 p
  rw [sub12718, sub12781]
  rfl
theorem sub12783 (p : Pattern) : d2973 (change p 10000 (some 204)) = d7060 p := by
  change (if p 161 then d2972 (change p 10000 (some 204)) else d2970 (change p 10000 (some 204))) = d7060 p
  rw [sub12782, sub12780]
  rfl
theorem sub12784 (p : Pattern) : d2974 (change p 10000 (some 204)) = d7061 p := by
  change (if p 163 then d12 (change p 10000 (some 204)) else d2963 (change p 10000 (some 204))) = d7061 p
  rw [sub12617, sub12773]
  rfl
theorem sub12785 (p : Pattern) : d2975 (change p 10000 (some 204)) = d7062 p := by
  change (if p 162 then d12 (change p 10000 (some 204)) else d2974 (change p 10000 (some 204))) = d7062 p
  rw [sub12617, sub12784]
  rfl
theorem sub12786 (p : Pattern) : d2976 (change p 10000 (some 204)) = d7063 p := by
  change (if p 161 then d12 (change p 10000 (some 204)) else d2975 (change p 10000 (some 204))) = d7063 p
  rw [sub12617, sub12785]
  rfl
theorem sub12787 (p : Pattern) : d2977 (change p 10000 (some 204)) = d7064 p := by
  change (if p 160 then d2976 (change p 10000 (some 204)) else d2973 (change p 10000 (some 204))) = d7064 p
  rw [sub12786, sub12783]
  rfl
theorem sub12788 (p : Pattern) : d2978 (change p 10000 (some 204)) = d7065 p := by
  change (if p 141 then d2977 (change p 10000 (some 204)) else d2967 (change p 10000 (some 204))) = d7065 p
  rw [sub12787, sub12777]
  rfl
theorem sub12789 (p : Pattern) : d2979 (change p 10000 (some 204)) = d7066 p := by
  change (if p 138 then d2978 (change p 10000 (some 204)) else d2947 (change p 10000 (some 204))) = d7066 p
  rw [sub12788, sub12739]
  rfl
theorem sub12790 (p : Pattern) : d2980 (change p 10000 (some 204)) = d7067 p := by
  change (if p 163 then d2931 (change p 10000 (some 204)) else d2957 (change p 10000 (some 204))) = d7067 p
  rw [sub12717, sub12760]
  rfl
theorem sub12791 (p : Pattern) : d2981 (change p 10000 (some 204)) = d7068 p := by
  change (if p 162 then d2932 (change p 10000 (some 204)) else d2980 (change p 10000 (some 204))) = d7068 p
  rw [sub12718, sub12790]
  rfl
theorem sub12792 (p : Pattern) : d2982 (change p 10000 (some 204)) = d7069 p := by
  change (if p 162 then d12 (change p 10000 (some 204)) else d2932 (change p 10000 (some 204))) = d7069 p
  rw [sub12617, sub12718]
  rfl
theorem sub12793 (p : Pattern) : d2983 (change p 10000 (some 204)) = d7070 p := by
  change (if p 161 then d2982 (change p 10000 (some 204)) else d2981 (change p 10000 (some 204))) = d7070 p
  rw [sub12792, sub12791]
  rfl
theorem sub12794 (p : Pattern) : d2984 (change p 10000 (some 204)) = d7071 p := by
  change (if p 161 then d12 (change p 10000 (some 204)) else d2982 (change p 10000 (some 204))) = d7071 p
  rw [sub12617, sub12792]
  rfl
theorem sub12795 (p : Pattern) : d2985 (change p 10000 (some 204)) = d7072 p := by
  change (if p 160 then d2984 (change p 10000 (some 204)) else d2983 (change p 10000 (some 204))) = d7072 p
  rw [sub12794, sub12793]
  rfl
theorem sub12796 (p : Pattern) : d2986 (change p 10000 (some 204)) = d7073 p := by
  change (if p 160 then d12 (change p 10000 (some 204)) else d2984 (change p 10000 (some 204))) = d7073 p
  rw [sub12617, sub12794]
  rfl
theorem sub12797 (p : Pattern) : d2987 (change p 10000 (some 204)) = d7074 p := by
  change (if p 141 then d2986 (change p 10000 (some 204)) else d2985 (change p 10000 (some 204))) = d7074 p
  rw [sub12796, sub12795]
  rfl
theorem sub12798 (p : Pattern) : d2988 (change p 10000 (some 204)) = d7075 p := by
  change (if p 138 then d2987 (change p 10000 (some 204)) else d2978 (change p 10000 (some 204))) = d7075 p
  rw [sub12797, sub12788]
  rfl
theorem sub12799 (p : Pattern) : d2989 (change p 10000 (some 204)) = d7076 p := by
  change (if p 116 then d2988 (change p 10000 (some 204)) else d2979 (change p 10000 (some 204))) = d7076 p
  rw [sub12798, sub12789]
  rfl
theorem sub12800 (p : Pattern) : d2990 (change p 10000 (some 204)) = d7077 p := by
  change (if p 138 then d12 (change p 10000 (some 204)) else d2978 (change p 10000 (some 204))) = d7077 p
  rw [sub12617, sub12788]
  rfl
theorem sub12801 (p : Pattern) : d2991 (change p 10000 (some 204)) = d7078 p := by
  change (if p 116 then d2990 (change p 10000 (some 204)) else d2979 (change p 10000 (some 204))) = d7078 p
  rw [sub12800, sub12789]
  rfl
theorem sub12802 (p : Pattern) : d2992 (change p 10000 (some 204)) = d7079 p := by
  change (if p 115 then d2991 (change p 10000 (some 204)) else d2989 (change p 10000 (some 204))) = d7079 p
  rw [sub12801, sub12799]
  rfl
theorem sub12803 (p : Pattern) : d1 (change p 10000 (some 204)) = d1 p := by
  rfl
theorem sub12804 (p : Pattern) : d102 (change p 10000 (some 204)) = d102 p := by
  change (if p 247 then d12 (change p 10000 (some 204)) else d1 (change p 10000 (some 204))) = d102 p
  rw [sub12617, sub12803]
  rfl
theorem sub12805 (p : Pattern) : d103 (change p 10000 (some 204)) = d103 p := by
  change (if p 246 then d102 (change p 10000 (some 204)) else d1 (change p 10000 (some 204))) = d103 p
  rw [sub12804, sub12803]
  rfl
theorem sub12806 (p : Pattern) : d5 (change p 10000 (some 204)) = d5 p := by
  rfl
theorem sub12807 (p : Pattern) : d1939 (change p 10000 (some 204)) = d1939 p := by
  change (if p 247 then d5 (change p 10000 (some 204)) else d1 (change p 10000 (some 204))) = d1939 p
  rw [sub12806, sub12803]
  rfl
theorem sub12808 (p : Pattern) : d106 (change p 10000 (some 204)) = d106 p := by
  change (if p 247 then d12 (change p 10000 (some 204)) else d5 (change p 10000 (some 204))) = d106 p
  rw [sub12617, sub12806]
  rfl
theorem sub12809 (p : Pattern) : d1940 (change p 10000 (some 204)) = d1940 p := by
  change (if p 246 then d106 (change p 10000 (some 204)) else d1939 (change p 10000 (some 204))) = d1940 p
  rw [sub12808, sub12807]
  rfl
theorem sub12810 (p : Pattern) : d1941 (change p 10000 (some 204)) = d1941 p := by
  change (if p 225 then d1940 (change p 10000 (some 204)) else d103 (change p 10000 (some 204))) = d1941 p
  rw [sub12809, sub12805]
  rfl
theorem sub12811 (p : Pattern) : d1942 (change p 10000 (some 204)) = d1942 p := by
  change (if p 224 then d1940 (change p 10000 (some 204)) else d1941 (change p 10000 (some 204))) = d1942 p
  rw [sub12809, sub12810]
  rfl
theorem sub12812 (p : Pattern) : d2993 (change p 10000 (some 204)) = d1942 p := by
  change d1942 (change p 10000 (some 204)) = d1942 p
  exact sub12811 p
theorem sub12813 (p : Pattern) : d1876 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12814 (p : Pattern) : d2994 (change p 10000 (some 204)) = d7080 p := by
  change (if p 182 then d1876 (change p 10000 (some 204)) else d2993 (change p 10000 (some 204))) = d7080 p
  rw [sub12813, sub12812]
  rfl
theorem sub12815 (p : Pattern) : d107 (change p 10000 (some 204)) = d107 p := by
  change (if p 246 then d106 (change p 10000 (some 204)) else d5 (change p 10000 (some 204))) = d107 p
  rw [sub12808, sub12806]
  rfl
theorem sub12816 (p : Pattern) : d1963 (change p 10000 (some 204)) = d1963 p := by
  change (if p 247 then d9 (change p 10000 (some 204)) else d5 (change p 10000 (some 204))) = d1963 p
  rw [sub12641, sub12806]
  rfl
theorem sub12817 (p : Pattern) : d1964 (change p 10000 (some 204)) = d1964 p := by
  change (if p 246 then d23 (change p 10000 (some 204)) else d1963 (change p 10000 (some 204))) = d1964 p
  rw [sub12642, sub12816]
  rfl
theorem sub12818 (p : Pattern) : d2129 (change p 10000 (some 204)) = d2129 p := by
  change (if p 225 then d1964 (change p 10000 (some 204)) else d107 (change p 10000 (some 204))) = d2129 p
  rw [sub12817, sub12815]
  rfl
theorem sub12819 (p : Pattern) : d2130 (change p 10000 (some 204)) = d2130 p := by
  change (if p 224 then d1964 (change p 10000 (some 204)) else d2129 (change p 10000 (some 204))) = d2130 p
  rw [sub12817, sub12818]
  rfl
theorem sub12820 (p : Pattern) : d2995 (change p 10000 (some 204)) = d2130 p := by
  change d2130 (change p 10000 (some 204)) = d2130 p
  exact sub12819 p
theorem sub12821 (p : Pattern) : d1884 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12822 (p : Pattern) : d2996 (change p 10000 (some 204)) = d7081 p := by
  change (if p 182 then d1884 (change p 10000 (some 204)) else d2995 (change p 10000 (some 204))) = d7081 p
  rw [sub12821, sub12820]
  rfl
theorem sub12823 (p : Pattern) : d2997 (change p 10000 (some 204)) = d7082 p := by
  change (if p 163 then d2996 (change p 10000 (some 204)) else d2994 (change p 10000 (some 204))) = d7082 p
  rw [sub12822, sub12814]
  rfl
theorem sub12824 (p : Pattern) : d2998 (change p 10000 (some 204)) = d7083 p := by
  change (if p 162 then d2997 (change p 10000 (some 204)) else d2994 (change p 10000 (some 204))) = d7083 p
  rw [sub12823, sub12814]
  rfl
theorem sub12825 (p : Pattern) : d2999 (change p 10000 (some 204)) = d7084 p := by
  change (if p 163 then d12 (change p 10000 (some 204)) else d2928 (change p 10000 (some 204))) = d7084 p
  rw [sub12617, sub12709]
  rfl
theorem sub12826 (p : Pattern) : d3000 (change p 10000 (some 204)) = d7085 p := by
  change (if p 162 then d2999 (change p 10000 (some 204)) else d2997 (change p 10000 (some 204))) = d7085 p
  rw [sub12825, sub12823]
  rfl
theorem sub12827 (p : Pattern) : d3001 (change p 10000 (some 204)) = d7086 p := by
  change (if p 161 then d3000 (change p 10000 (some 204)) else d2998 (change p 10000 (some 204))) = d7086 p
  rw [sub12826, sub12824]
  rfl
theorem sub12828 (p : Pattern) : d7 (change p 10000 (some 204)) = d7 p := by
  rfl
theorem sub12829 (p : Pattern) : d1945 (change p 10000 (some 204)) = d1945 p := by
  change (if p 247 then d7 (change p 10000 (some 204)) else d1 (change p 10000 (some 204))) = d1945 p
  rw [sub12828, sub12803]
  rfl
theorem sub12830 (p : Pattern) : d119 (change p 10000 (some 204)) = d119 p := by
  change (if p 247 then d12 (change p 10000 (some 204)) else d7 (change p 10000 (some 204))) = d119 p
  rw [sub12617, sub12828]
  rfl
theorem sub12831 (p : Pattern) : d1946 (change p 10000 (some 204)) = d1946 p := by
  change (if p 246 then d119 (change p 10000 (some 204)) else d1945 (change p 10000 (some 204))) = d1946 p
  rw [sub12830, sub12829]
  rfl
theorem sub12832 (p : Pattern) : d1947 (change p 10000 (some 204)) = d1947 p := by
  change (if p 225 then d1946 (change p 10000 (some 204)) else d103 (change p 10000 (some 204))) = d1947 p
  rw [sub12831, sub12805]
  rfl
theorem sub12833 (p : Pattern) : d1955 (change p 10000 (some 204)) = d1955 p := by
  change (if p 246 then d57 (change p 10000 (some 204)) else d102 (change p 10000 (some 204))) = d1955 p
  rw [sub12673, sub12804]
  rfl
theorem sub12834 (p : Pattern) : d1956 (change p 10000 (some 204)) = d1956 p := by
  change (if p 225 then d1955 (change p 10000 (some 204)) else d1940 (change p 10000 (some 204))) = d1956 p
  rw [sub12833, sub12809]
  rfl
theorem sub12835 (p : Pattern) : d1957 (change p 10000 (some 204)) = d1957 p := by
  change (if p 224 then d1956 (change p 10000 (some 204)) else d1947 (change p 10000 (some 204))) = d1957 p
  rw [sub12834, sub12832]
  rfl
theorem sub12836 (p : Pattern) : d3002 (change p 10000 (some 204)) = d1957 p := by
  change d1957 (change p 10000 (some 204)) = d1957 p
  exact sub12835 p
theorem sub12837 (p : Pattern) : d1899 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12838 (p : Pattern) : d3003 (change p 10000 (some 204)) = d7087 p := by
  change (if p 182 then d1899 (change p 10000 (some 204)) else d3002 (change p 10000 (some 204))) = d7087 p
  rw [sub12837, sub12836]
  rfl
theorem sub12839 (p : Pattern) : d1906 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
end NetHack.Sokoban22Refined85
