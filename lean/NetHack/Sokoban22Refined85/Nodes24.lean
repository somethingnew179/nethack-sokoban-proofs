/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d2880 (p : Pattern) : Int := if p 162 then d2879 p else d2746 p
theorem agree2880 (p q : Pattern) (h : Agree support p q) : d2880 p = d2880 q := by
  simp only [d2880, h 162 (by decide), agree2879 p q h, agree2746 p q h]
theorem nonnegative2880 (p : Pattern) : 0 ≤ d2880 p :=
  nonnegative_ite (p 162) (nonnegative2879 p) (nonnegative2746 p)
def d2881 (p : Pattern) : Int := if p 163 then d2607 p else d2748 p
theorem agree2881 (p q : Pattern) (h : Agree support p q) : d2881 p = d2881 q := by
  simp only [d2881, h 163 (by decide), agree2607 p q h, agree2748 p q h]
theorem nonnegative2881 (p : Pattern) : 0 ≤ d2881 p :=
  nonnegative_ite (p 163) (nonnegative2607 p) (nonnegative2748 p)
def d2882 (p : Pattern) : Int := if p 162 then d12 p else d2881 p
theorem agree2882 (p q : Pattern) (h : Agree support p q) : d2882 p = d2882 q := by
  simp only [d2882, h 162 (by decide), agree12 p q h, agree2881 p q h]
theorem nonnegative2882 (p : Pattern) : 0 ≤ d2882 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2881 p)
def d2883 (p : Pattern) : Int := if p 161 then d2882 p else d2880 p
theorem agree2883 (p q : Pattern) (h : Agree support p q) : d2883 p = d2883 q := by
  simp only [d2883, h 161 (by decide), agree2882 p q h, agree2880 p q h]
theorem nonnegative2883 (p : Pattern) : 0 ≤ d2883 p :=
  nonnegative_ite (p 161) (nonnegative2882 p) (nonnegative2880 p)
def d2884 (p : Pattern) : Int := if p 163 then d2584 p else d2755 p
theorem agree2884 (p q : Pattern) (h : Agree support p q) : d2884 p = d2884 q := by
  simp only [d2884, h 163 (by decide), agree2584 p q h, agree2755 p q h]
theorem nonnegative2884 (p : Pattern) : 0 ≤ d2884 p :=
  nonnegative_ite (p 163) (nonnegative2584 p) (nonnegative2755 p)
def d2885 (p : Pattern) : Int := if p 162 then d12 p else d2884 p
theorem agree2885 (p q : Pattern) (h : Agree support p q) : d2885 p = d2885 q := by
  simp only [d2885, h 162 (by decide), agree12 p q h, agree2884 p q h]
theorem nonnegative2885 (p : Pattern) : 0 ≤ d2885 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2884 p)
def d2886 (p : Pattern) : Int := if p 161 then d12 p else d2885 p
theorem agree2886 (p q : Pattern) (h : Agree support p q) : d2886 p = d2886 q := by
  simp only [d2886, h 161 (by decide), agree12 p q h, agree2885 p q h]
theorem nonnegative2886 (p : Pattern) : 0 ≤ d2886 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2885 p)
def d2887 (p : Pattern) : Int := if p 160 then d2886 p else d2883 p
theorem agree2887 (p q : Pattern) (h : Agree support p q) : d2887 p = d2887 q := by
  simp only [d2887, h 160 (by decide), agree2886 p q h, agree2883 p q h]
theorem nonnegative2887 (p : Pattern) : 0 ≤ d2887 p :=
  nonnegative_ite (p 160) (nonnegative2886 p) (nonnegative2883 p)
def d2888 (p : Pattern) : Int := if p 141 then d2876 p else d2887 p
theorem agree2888 (p q : Pattern) (h : Agree support p q) : d2888 p = d2888 q := by
  simp only [d2888, h 141 (by decide), agree2876 p q h, agree2887 p q h]
theorem nonnegative2888 (p : Pattern) : 0 ≤ d2888 p :=
  nonnegative_ite (p 141) (nonnegative2876 p) (nonnegative2887 p)
def d2889 (p : Pattern) : Int := if p 138 then d12 p else d2888 p
theorem agree2889 (p q : Pattern) (h : Agree support p q) : d2889 p = d2889 q := by
  simp only [d2889, h 138 (by decide), agree12 p q h, agree2888 p q h]
theorem nonnegative2889 (p : Pattern) : 0 ≤ d2889 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative2888 p)
def d2890 (p : Pattern) : Int := if p 116 then d2889 p else d2878 p
theorem agree2890 (p q : Pattern) (h : Agree support p q) : d2890 p = d2890 q := by
  simp only [d2890, h 116 (by decide), agree2889 p q h, agree2878 p q h]
theorem nonnegative2890 (p : Pattern) : 0 ≤ d2890 p :=
  nonnegative_ite (p 116) (nonnegative2889 p) (nonnegative2878 p)
def d2891 (p : Pattern) : Int := if p 115 then d2890 p else d2852 p
theorem agree2891 (p q : Pattern) (h : Agree support p q) : d2891 p = d2891 q := by
  simp only [d2891, h 115 (by decide), agree2890 p q h, agree2852 p q h]
theorem nonnegative2891 (p : Pattern) : 0 ≤ d2891 p :=
  nonnegative_ite (p 115) (nonnegative2890 p) (nonnegative2852 p)
def d2892 (p : Pattern) : Int := if p 71 then d2891 p else d2652 p
theorem agree2892 (p q : Pattern) (h : Agree support p q) : d2892 p = d2892 q := by
  simp only [d2892, h 71 (by decide), agree2891 p q h, agree2652 p q h]
theorem nonnegative2892 (p : Pattern) : 0 ≤ d2892 p :=
  nonnegative_ite (p 71) (nonnegative2891 p) (nonnegative2652 p)
def d2893 (p : Pattern) : Int := if p 49 then d2892 p else d2833 p
theorem agree2893 (p q : Pattern) (h : Agree support p q) : d2893 p = d2893 q := by
  simp only [d2893, h 49 (by decide), agree2892 p q h, agree2833 p q h]
theorem nonnegative2893 (p : Pattern) : 0 ≤ d2893 p :=
  nonnegative_ite (p 49) (nonnegative2892 p) (nonnegative2833 p)
def d2894 (p : Pattern) : Int := if p 48 then d2893 p else d2791 p
theorem agree2894 (p q : Pattern) (h : Agree support p q) : d2894 p = d2894 q := by
  simp only [d2894, h 48 (by decide), agree2893 p q h, agree2791 p q h]
theorem nonnegative2894 (p : Pattern) : 0 ≤ d2894 p :=
  nonnegative_ite (p 48) (nonnegative2893 p) (nonnegative2791 p)
def d2895 (p : Pattern) : Int := if p 204 then d1772 p else d14 p
theorem agree2895 (p q : Pattern) (h : Agree support p q) : d2895 p = d2895 q := by
  simp only [d2895, h 204 (by decide), agree1772 p q h, agree14 p q h]
theorem nonnegative2895 (p : Pattern) : 0 ≤ d2895 p :=
  nonnegative_ite (p 204) (nonnegative1772 p) (nonnegative14 p)
def d2896 (p : Pattern) : Int := if p 182 then d1687 p else d2895 p
theorem agree2896 (p q : Pattern) (h : Agree support p q) : d2896 p = d2896 q := by
  simp only [d2896, h 182 (by decide), agree1687 p q h, agree2895 p q h]
theorem nonnegative2896 (p : Pattern) : 0 ≤ d2896 p :=
  nonnegative_ite (p 182) (nonnegative1687 p) (nonnegative2895 p)
def d2897 (p : Pattern) : Int := if p 204 then d2012 p else d18 p
theorem agree2897 (p q : Pattern) (h : Agree support p q) : d2897 p = d2897 q := by
  simp only [d2897, h 204 (by decide), agree2012 p q h, agree18 p q h]
theorem nonnegative2897 (p : Pattern) : 0 ≤ d2897 p :=
  nonnegative_ite (p 204) (nonnegative2012 p) (nonnegative18 p)
def d2898 (p : Pattern) : Int := if p 182 then d1697 p else d2897 p
theorem agree2898 (p q : Pattern) (h : Agree support p q) : d2898 p = d2898 q := by
  simp only [d2898, h 182 (by decide), agree1697 p q h, agree2897 p q h]
theorem nonnegative2898 (p : Pattern) : 0 ≤ d2898 p :=
  nonnegative_ite (p 182) (nonnegative1697 p) (nonnegative2897 p)
def d2899 (p : Pattern) : Int := if p 163 then d2898 p else d2896 p
theorem agree2899 (p q : Pattern) (h : Agree support p q) : d2899 p = d2899 q := by
  simp only [d2899, h 163 (by decide), agree2898 p q h, agree2896 p q h]
theorem nonnegative2899 (p : Pattern) : 0 ≤ d2899 p :=
  nonnegative_ite (p 163) (nonnegative2898 p) (nonnegative2896 p)
def d2900 (p : Pattern) : Int := if p 162 then d2899 p else d2896 p
theorem agree2900 (p q : Pattern) (h : Agree support p q) : d2900 p = d2900 q := by
  simp only [d2900, h 162 (by decide), agree2899 p q h, agree2896 p q h]
theorem nonnegative2900 (p : Pattern) : 0 ≤ d2900 p :=
  nonnegative_ite (p 162) (nonnegative2899 p) (nonnegative2896 p)
def d2901 (p : Pattern) : Int := if p 204 then d1803 p else d24 p
theorem agree2901 (p q : Pattern) (h : Agree support p q) : d2901 p = d2901 q := by
  simp only [d2901, h 204 (by decide), agree1803 p q h, agree24 p q h]
theorem nonnegative2901 (p : Pattern) : 0 ≤ d2901 p :=
  nonnegative_ite (p 204) (nonnegative1803 p) (nonnegative24 p)
def d2902 (p : Pattern) : Int := if p 182 then d1705 p else d2901 p
theorem agree2902 (p q : Pattern) (h : Agree support p q) : d2902 p = d2902 q := by
  simp only [d2902, h 182 (by decide), agree1705 p q h, agree2901 p q h]
theorem nonnegative2902 (p : Pattern) : 0 ≤ d2902 p :=
  nonnegative_ite (p 182) (nonnegative1705 p) (nonnegative2901 p)
def d2903 (p : Pattern) : Int := if p 163 then d12 p else d2902 p
theorem agree2903 (p q : Pattern) (h : Agree support p q) : d2903 p = d2903 q := by
  simp only [d2903, h 163 (by decide), agree12 p q h, agree2902 p q h]
theorem nonnegative2903 (p : Pattern) : 0 ≤ d2903 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2902 p)
def d2904 (p : Pattern) : Int := if p 162 then d2903 p else d2899 p
theorem agree2904 (p q : Pattern) (h : Agree support p q) : d2904 p = d2904 q := by
  simp only [d2904, h 162 (by decide), agree2903 p q h, agree2899 p q h]
theorem nonnegative2904 (p : Pattern) : 0 ≤ d2904 p :=
  nonnegative_ite (p 162) (nonnegative2903 p) (nonnegative2899 p)
def d2905 (p : Pattern) : Int := if p 161 then d2904 p else d2900 p
theorem agree2905 (p q : Pattern) (h : Agree support p q) : d2905 p = d2905 q := by
  simp only [d2905, h 161 (by decide), agree2904 p q h, agree2900 p q h]
theorem nonnegative2905 (p : Pattern) : 0 ≤ d2905 p :=
  nonnegative_ite (p 161) (nonnegative2904 p) (nonnegative2900 p)
def d2906 (p : Pattern) : Int := if p 204 then d1788 p else d14 p
theorem agree2906 (p q : Pattern) (h : Agree support p q) : d2906 p = d2906 q := by
  simp only [d2906, h 204 (by decide), agree1788 p q h, agree14 p q h]
theorem nonnegative2906 (p : Pattern) : 0 ≤ d2906 p :=
  nonnegative_ite (p 204) (nonnegative1788 p) (nonnegative14 p)
def d2907 (p : Pattern) : Int := if p 182 then d1718 p else d2906 p
theorem agree2907 (p q : Pattern) (h : Agree support p q) : d2907 p = d2907 q := by
  simp only [d2907, h 182 (by decide), agree1718 p q h, agree2906 p q h]
theorem nonnegative2907 (p : Pattern) : 0 ≤ d2907 p :=
  nonnegative_ite (p 182) (nonnegative1718 p) (nonnegative2906 p)
def d2908 (p : Pattern) : Int := if p 182 then d1725 p else d2906 p
theorem agree2908 (p q : Pattern) (h : Agree support p q) : d2908 p = d2908 q := by
  simp only [d2908, h 182 (by decide), agree1725 p q h, agree2906 p q h]
theorem nonnegative2908 (p : Pattern) : 0 ≤ d2908 p :=
  nonnegative_ite (p 182) (nonnegative1725 p) (nonnegative2906 p)
def d2909 (p : Pattern) : Int := if p 163 then d2908 p else d2907 p
theorem agree2909 (p q : Pattern) (h : Agree support p q) : d2909 p = d2909 q := by
  simp only [d2909, h 163 (by decide), agree2908 p q h, agree2907 p q h]
theorem nonnegative2909 (p : Pattern) : 0 ≤ d2909 p :=
  nonnegative_ite (p 163) (nonnegative2908 p) (nonnegative2907 p)
def d2910 (p : Pattern) : Int := if p 182 then d1730 p else d2906 p
theorem agree2910 (p q : Pattern) (h : Agree support p q) : d2910 p = d2910 q := by
  simp only [d2910, h 182 (by decide), agree1730 p q h, agree2906 p q h]
theorem nonnegative2910 (p : Pattern) : 0 ≤ d2910 p :=
  nonnegative_ite (p 182) (nonnegative1730 p) (nonnegative2906 p)
def d2911 (p : Pattern) : Int := if p 204 then d1797 p else d18 p
theorem agree2911 (p q : Pattern) (h : Agree support p q) : d2911 p = d2911 q := by
  simp only [d2911, h 204 (by decide), agree1797 p q h, agree18 p q h]
theorem nonnegative2911 (p : Pattern) : 0 ≤ d2911 p :=
  nonnegative_ite (p 204) (nonnegative1797 p) (nonnegative18 p)
def d2912 (p : Pattern) : Int := if p 182 then d12 p else d2911 p
theorem agree2912 (p q : Pattern) (h : Agree support p q) : d2912 p = d2912 q := by
  simp only [d2912, h 182 (by decide), agree12 p q h, agree2911 p q h]
theorem nonnegative2912 (p : Pattern) : 0 ≤ d2912 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2911 p)
def d2913 (p : Pattern) : Int := if p 163 then d2912 p else d2910 p
theorem agree2913 (p q : Pattern) (h : Agree support p q) : d2913 p = d2913 q := by
  simp only [d2913, h 163 (by decide), agree2912 p q h, agree2910 p q h]
theorem nonnegative2913 (p : Pattern) : 0 ≤ d2913 p :=
  nonnegative_ite (p 163) (nonnegative2912 p) (nonnegative2910 p)
def d2914 (p : Pattern) : Int := if p 162 then d2913 p else d2909 p
theorem agree2914 (p q : Pattern) (h : Agree support p q) : d2914 p = d2914 q := by
  simp only [d2914, h 162 (by decide), agree2913 p q h, agree2909 p q h]
theorem nonnegative2914 (p : Pattern) : 0 ≤ d2914 p :=
  nonnegative_ite (p 162) (nonnegative2913 p) (nonnegative2909 p)
def d2915 (p : Pattern) : Int := if p 182 then d12 p else d2906 p
theorem agree2915 (p q : Pattern) (h : Agree support p q) : d2915 p = d2915 q := by
  simp only [d2915, h 182 (by decide), agree12 p q h, agree2906 p q h]
theorem nonnegative2915 (p : Pattern) : 0 ≤ d2915 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2906 p)
def d2916 (p : Pattern) : Int := if p 163 then d2912 p else d2915 p
theorem agree2916 (p q : Pattern) (h : Agree support p q) : d2916 p = d2916 q := by
  simp only [d2916, h 163 (by decide), agree2912 p q h, agree2915 p q h]
theorem nonnegative2916 (p : Pattern) : 0 ≤ d2916 p :=
  nonnegative_ite (p 163) (nonnegative2912 p) (nonnegative2915 p)
def d2917 (p : Pattern) : Int := if p 182 then d12 p else d2901 p
theorem agree2917 (p q : Pattern) (h : Agree support p q) : d2917 p = d2917 q := by
  simp only [d2917, h 182 (by decide), agree12 p q h, agree2901 p q h]
theorem nonnegative2917 (p : Pattern) : 0 ≤ d2917 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2901 p)
def d2918 (p : Pattern) : Int := if p 163 then d12 p else d2917 p
theorem agree2918 (p q : Pattern) (h : Agree support p q) : d2918 p = d2918 q := by
  simp only [d2918, h 163 (by decide), agree12 p q h, agree2917 p q h]
theorem nonnegative2918 (p : Pattern) : 0 ≤ d2918 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2917 p)
def d2919 (p : Pattern) : Int := if p 162 then d2918 p else d2916 p
theorem agree2919 (p q : Pattern) (h : Agree support p q) : d2919 p = d2919 q := by
  simp only [d2919, h 162 (by decide), agree2918 p q h, agree2916 p q h]
theorem nonnegative2919 (p : Pattern) : 0 ≤ d2919 p :=
  nonnegative_ite (p 162) (nonnegative2918 p) (nonnegative2916 p)
def d2920 (p : Pattern) : Int := if p 161 then d2919 p else d2914 p
theorem agree2920 (p q : Pattern) (h : Agree support p q) : d2920 p = d2920 q := by
  simp only [d2920, h 161 (by decide), agree2919 p q h, agree2914 p q h]
theorem nonnegative2920 (p : Pattern) : 0 ≤ d2920 p :=
  nonnegative_ite (p 161) (nonnegative2919 p) (nonnegative2914 p)
def d2921 (p : Pattern) : Int := if p 160 then d2920 p else d2905 p
theorem agree2921 (p q : Pattern) (h : Agree support p q) : d2921 p = d2921 q := by
  simp only [d2921, h 160 (by decide), agree2920 p q h, agree2905 p q h]
theorem nonnegative2921 (p : Pattern) : 0 ≤ d2921 p :=
  nonnegative_ite (p 160) (nonnegative2920 p) (nonnegative2905 p)
def d2922 (p : Pattern) : Int := if p 204 then d2030 p else d31 p
theorem agree2922 (p q : Pattern) (h : Agree support p q) : d2922 p = d2922 q := by
  simp only [d2922, h 204 (by decide), agree2030 p q h, agree31 p q h]
theorem nonnegative2922 (p : Pattern) : 0 ≤ d2922 p :=
  nonnegative_ite (p 204) (nonnegative2030 p) (nonnegative31 p)
def d2923 (p : Pattern) : Int := if p 182 then d1746 p else d2922 p
theorem agree2923 (p q : Pattern) (h : Agree support p q) : d2923 p = d2923 q := by
  simp only [d2923, h 182 (by decide), agree1746 p q h, agree2922 p q h]
theorem nonnegative2923 (p : Pattern) : 0 ≤ d2923 p :=
  nonnegative_ite (p 182) (nonnegative1746 p) (nonnegative2922 p)
def d2924 (p : Pattern) : Int := if p 163 then d2923 p else d2896 p
theorem agree2924 (p q : Pattern) (h : Agree support p q) : d2924 p = d2924 q := by
  simp only [d2924, h 163 (by decide), agree2923 p q h, agree2896 p q h]
theorem nonnegative2924 (p : Pattern) : 0 ≤ d2924 p :=
  nonnegative_ite (p 163) (nonnegative2923 p) (nonnegative2896 p)
def d2925 (p : Pattern) : Int := if p 163 then d2902 p else d2898 p
theorem agree2925 (p q : Pattern) (h : Agree support p q) : d2925 p = d2925 q := by
  simp only [d2925, h 163 (by decide), agree2902 p q h, agree2898 p q h]
theorem nonnegative2925 (p : Pattern) : 0 ≤ d2925 p :=
  nonnegative_ite (p 163) (nonnegative2902 p) (nonnegative2898 p)
def d2926 (p : Pattern) : Int := if p 162 then d2925 p else d2924 p
theorem agree2926 (p q : Pattern) (h : Agree support p q) : d2926 p = d2926 q := by
  simp only [d2926, h 162 (by decide), agree2925 p q h, agree2924 p q h]
theorem nonnegative2926 (p : Pattern) : 0 ≤ d2926 p :=
  nonnegative_ite (p 162) (nonnegative2925 p) (nonnegative2924 p)
def d2927 (p : Pattern) : Int := if p 204 then d1752 p else d58 p
theorem agree2927 (p q : Pattern) (h : Agree support p q) : d2927 p = d2927 q := by
  simp only [d2927, h 204 (by decide), agree1752 p q h, agree58 p q h]
theorem nonnegative2927 (p : Pattern) : 0 ≤ d2927 p :=
  nonnegative_ite (p 204) (nonnegative1752 p) (nonnegative58 p)
def d2928 (p : Pattern) : Int := if p 182 then d1753 p else d2927 p
theorem agree2928 (p q : Pattern) (h : Agree support p q) : d2928 p = d2928 q := by
  simp only [d2928, h 182 (by decide), agree1753 p q h, agree2927 p q h]
theorem nonnegative2928 (p : Pattern) : 0 ≤ d2928 p :=
  nonnegative_ite (p 182) (nonnegative1753 p) (nonnegative2927 p)
def d2929 (p : Pattern) : Int := if p 163 then d2928 p else d2898 p
theorem agree2929 (p q : Pattern) (h : Agree support p q) : d2929 p = d2929 q := by
  simp only [d2929, h 163 (by decide), agree2928 p q h, agree2898 p q h]
theorem nonnegative2929 (p : Pattern) : 0 ≤ d2929 p :=
  nonnegative_ite (p 163) (nonnegative2928 p) (nonnegative2898 p)
def d2930 (p : Pattern) : Int := if p 204 then d1729 p else d40 p
theorem agree2930 (p q : Pattern) (h : Agree support p q) : d2930 p = d2930 q := by
  simp only [d2930, h 204 (by decide), agree1729 p q h, agree40 p q h]
theorem nonnegative2930 (p : Pattern) : 0 ≤ d2930 p :=
  nonnegative_ite (p 204) (nonnegative1729 p) (nonnegative40 p)
def d2931 (p : Pattern) : Int := if p 182 then d1730 p else d2930 p
theorem agree2931 (p q : Pattern) (h : Agree support p q) : d2931 p = d2931 q := by
  simp only [d2931, h 182 (by decide), agree1730 p q h, agree2930 p q h]
theorem nonnegative2931 (p : Pattern) : 0 ≤ d2931 p :=
  nonnegative_ite (p 182) (nonnegative1730 p) (nonnegative2930 p)
def d2932 (p : Pattern) : Int := if p 163 then d12 p else d2931 p
theorem agree2932 (p q : Pattern) (h : Agree support p q) : d2932 p = d2932 q := by
  simp only [d2932, h 163 (by decide), agree12 p q h, agree2931 p q h]
theorem nonnegative2932 (p : Pattern) : 0 ≤ d2932 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2931 p)
def d2933 (p : Pattern) : Int := if p 162 then d2932 p else d2929 p
theorem agree2933 (p q : Pattern) (h : Agree support p q) : d2933 p = d2933 q := by
  simp only [d2933, h 162 (by decide), agree2932 p q h, agree2929 p q h]
theorem nonnegative2933 (p : Pattern) : 0 ≤ d2933 p :=
  nonnegative_ite (p 162) (nonnegative2932 p) (nonnegative2929 p)
def d2934 (p : Pattern) : Int := if p 161 then d2933 p else d2926 p
theorem agree2934 (p q : Pattern) (h : Agree support p q) : d2934 p = d2934 q := by
  simp only [d2934, h 161 (by decide), agree2933 p q h, agree2926 p q h]
theorem nonnegative2934 (p : Pattern) : 0 ≤ d2934 p :=
  nonnegative_ite (p 161) (nonnegative2933 p) (nonnegative2926 p)
def d2935 (p : Pattern) : Int := if p 204 then d1717 p else d31 p
theorem agree2935 (p q : Pattern) (h : Agree support p q) : d2935 p = d2935 q := by
  simp only [d2935, h 204 (by decide), agree1717 p q h, agree31 p q h]
theorem nonnegative2935 (p : Pattern) : 0 ≤ d2935 p :=
  nonnegative_ite (p 204) (nonnegative1717 p) (nonnegative31 p)
def d2936 (p : Pattern) : Int := if p 182 then d12 p else d2935 p
theorem agree2936 (p q : Pattern) (h : Agree support p q) : d2936 p = d2936 q := by
  simp only [d2936, h 182 (by decide), agree12 p q h, agree2935 p q h]
theorem nonnegative2936 (p : Pattern) : 0 ≤ d2936 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2935 p)
def d2937 (p : Pattern) : Int := if p 163 then d2936 p else d2908 p
theorem agree2937 (p q : Pattern) (h : Agree support p q) : d2937 p = d2937 q := by
  simp only [d2937, h 163 (by decide), agree2936 p q h, agree2908 p q h]
theorem nonnegative2937 (p : Pattern) : 0 ≤ d2937 p :=
  nonnegative_ite (p 163) (nonnegative2936 p) (nonnegative2908 p)
def d2938 (p : Pattern) : Int := if p 163 then d2917 p else d2912 p
theorem agree2938 (p q : Pattern) (h : Agree support p q) : d2938 p = d2938 q := by
  simp only [d2938, h 163 (by decide), agree2917 p q h, agree2912 p q h]
theorem nonnegative2938 (p : Pattern) : 0 ≤ d2938 p :=
  nonnegative_ite (p 163) (nonnegative2917 p) (nonnegative2912 p)
def d2939 (p : Pattern) : Int := if p 162 then d2938 p else d2937 p
theorem agree2939 (p q : Pattern) (h : Agree support p q) : d2939 p = d2939 q := by
  simp only [d2939, h 162 (by decide), agree2938 p q h, agree2937 p q h]
theorem nonnegative2939 (p : Pattern) : 0 ≤ d2939 p :=
  nonnegative_ite (p 162) (nonnegative2938 p) (nonnegative2937 p)
def d2940 (p : Pattern) : Int := if p 182 then d12 p else d2927 p
theorem agree2940 (p q : Pattern) (h : Agree support p q) : d2940 p = d2940 q := by
  simp only [d2940, h 182 (by decide), agree12 p q h, agree2927 p q h]
theorem nonnegative2940 (p : Pattern) : 0 ≤ d2940 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2927 p)
def d2941 (p : Pattern) : Int := if p 163 then d2940 p else d2912 p
theorem agree2941 (p q : Pattern) (h : Agree support p q) : d2941 p = d2941 q := by
  simp only [d2941, h 163 (by decide), agree2940 p q h, agree2912 p q h]
theorem nonnegative2941 (p : Pattern) : 0 ≤ d2941 p :=
  nonnegative_ite (p 163) (nonnegative2940 p) (nonnegative2912 p)
def d2942 (p : Pattern) : Int := if p 182 then d12 p else d2930 p
theorem agree2942 (p q : Pattern) (h : Agree support p q) : d2942 p = d2942 q := by
  simp only [d2942, h 182 (by decide), agree12 p q h, agree2930 p q h]
theorem nonnegative2942 (p : Pattern) : 0 ≤ d2942 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2930 p)
def d2943 (p : Pattern) : Int := if p 163 then d12 p else d2942 p
theorem agree2943 (p q : Pattern) (h : Agree support p q) : d2943 p = d2943 q := by
  simp only [d2943, h 163 (by decide), agree12 p q h, agree2942 p q h]
theorem nonnegative2943 (p : Pattern) : 0 ≤ d2943 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2942 p)
def d2944 (p : Pattern) : Int := if p 162 then d2943 p else d2941 p
theorem agree2944 (p q : Pattern) (h : Agree support p q) : d2944 p = d2944 q := by
  simp only [d2944, h 162 (by decide), agree2943 p q h, agree2941 p q h]
theorem nonnegative2944 (p : Pattern) : 0 ≤ d2944 p :=
  nonnegative_ite (p 162) (nonnegative2943 p) (nonnegative2941 p)
def d2945 (p : Pattern) : Int := if p 161 then d2944 p else d2939 p
theorem agree2945 (p q : Pattern) (h : Agree support p q) : d2945 p = d2945 q := by
  simp only [d2945, h 161 (by decide), agree2944 p q h, agree2939 p q h]
theorem nonnegative2945 (p : Pattern) : 0 ≤ d2945 p :=
  nonnegative_ite (p 161) (nonnegative2944 p) (nonnegative2939 p)
def d2946 (p : Pattern) : Int := if p 160 then d2945 p else d2934 p
theorem agree2946 (p q : Pattern) (h : Agree support p q) : d2946 p = d2946 q := by
  simp only [d2946, h 160 (by decide), agree2945 p q h, agree2934 p q h]
theorem nonnegative2946 (p : Pattern) : 0 ≤ d2946 p :=
  nonnegative_ite (p 160) (nonnegative2945 p) (nonnegative2934 p)
def d2947 (p : Pattern) : Int := if p 141 then d2946 p else d2921 p
theorem agree2947 (p q : Pattern) (h : Agree support p q) : d2947 p = d2947 q := by
  simp only [d2947, h 141 (by decide), agree2946 p q h, agree2921 p q h]
theorem nonnegative2947 (p : Pattern) : 0 ≤ d2947 p :=
  nonnegative_ite (p 141) (nonnegative2946 p) (nonnegative2921 p)
def d2948 (p : Pattern) : Int := if p 204 then d2048 p else d14 p
theorem agree2948 (p q : Pattern) (h : Agree support p q) : d2948 p = d2948 q := by
  simp only [d2948, h 204 (by decide), agree2048 p q h, agree14 p q h]
theorem nonnegative2948 (p : Pattern) : 0 ≤ d2948 p :=
  nonnegative_ite (p 204) (nonnegative2048 p) (nonnegative14 p)
def d2949 (p : Pattern) : Int := if p 182 then d1773 p else d2948 p
theorem agree2949 (p q : Pattern) (h : Agree support p q) : d2949 p = d2949 q := by
  simp only [d2949, h 182 (by decide), agree1773 p q h, agree2948 p q h]
theorem nonnegative2949 (p : Pattern) : 0 ≤ d2949 p :=
  nonnegative_ite (p 182) (nonnegative1773 p) (nonnegative2948 p)
def d2950 (p : Pattern) : Int := if p 204 then d2054 p else d14 p
theorem agree2950 (p q : Pattern) (h : Agree support p q) : d2950 p = d2950 q := by
  simp only [d2950, h 204 (by decide), agree2054 p q h, agree14 p q h]
theorem nonnegative2950 (p : Pattern) : 0 ≤ d2950 p :=
  nonnegative_ite (p 204) (nonnegative2054 p) (nonnegative14 p)
def d2951 (p : Pattern) : Int := if p 182 then d1782 p else d2950 p
theorem agree2951 (p q : Pattern) (h : Agree support p q) : d2951 p = d2951 q := by
  simp only [d2951, h 182 (by decide), agree1782 p q h, agree2950 p q h]
theorem nonnegative2951 (p : Pattern) : 0 ≤ d2951 p :=
  nonnegative_ite (p 182) (nonnegative1782 p) (nonnegative2950 p)
def d2952 (p : Pattern) : Int := if p 163 then d2951 p else d2949 p
theorem agree2952 (p q : Pattern) (h : Agree support p q) : d2952 p = d2952 q := by
  simp only [d2952, h 163 (by decide), agree2951 p q h, agree2949 p q h]
theorem nonnegative2952 (p : Pattern) : 0 ≤ d2952 p :=
  nonnegative_ite (p 163) (nonnegative2951 p) (nonnegative2949 p)
def d2953 (p : Pattern) : Int := if p 182 then d1789 p else d2906 p
theorem agree2953 (p q : Pattern) (h : Agree support p q) : d2953 p = d2953 q := by
  simp only [d2953, h 182 (by decide), agree1789 p q h, agree2906 p q h]
theorem nonnegative2953 (p : Pattern) : 0 ≤ d2953 p :=
  nonnegative_ite (p 182) (nonnegative1789 p) (nonnegative2906 p)
def d2954 (p : Pattern) : Int := if p 182 then d1798 p else d2911 p
theorem agree2954 (p q : Pattern) (h : Agree support p q) : d2954 p = d2954 q := by
  simp only [d2954, h 182 (by decide), agree1798 p q h, agree2911 p q h]
theorem nonnegative2954 (p : Pattern) : 0 ≤ d2954 p :=
  nonnegative_ite (p 182) (nonnegative1798 p) (nonnegative2911 p)
def d2955 (p : Pattern) : Int := if p 163 then d2954 p else d2953 p
theorem agree2955 (p q : Pattern) (h : Agree support p q) : d2955 p = d2955 q := by
  simp only [d2955, h 163 (by decide), agree2954 p q h, agree2953 p q h]
theorem nonnegative2955 (p : Pattern) : 0 ≤ d2955 p :=
  nonnegative_ite (p 163) (nonnegative2954 p) (nonnegative2953 p)
def d2956 (p : Pattern) : Int := if p 162 then d2955 p else d2952 p
theorem agree2956 (p q : Pattern) (h : Agree support p q) : d2956 p = d2956 q := by
  simp only [d2956, h 162 (by decide), agree2955 p q h, agree2952 p q h]
theorem nonnegative2956 (p : Pattern) : 0 ≤ d2956 p :=
  nonnegative_ite (p 162) (nonnegative2955 p) (nonnegative2952 p)
def d2957 (p : Pattern) : Int := if p 182 then d1804 p else d2901 p
theorem agree2957 (p q : Pattern) (h : Agree support p q) : d2957 p = d2957 q := by
  simp only [d2957, h 182 (by decide), agree1804 p q h, agree2901 p q h]
theorem nonnegative2957 (p : Pattern) : 0 ≤ d2957 p :=
  nonnegative_ite (p 182) (nonnegative1804 p) (nonnegative2901 p)
def d2958 (p : Pattern) : Int := if p 163 then d12 p else d2957 p
theorem agree2958 (p q : Pattern) (h : Agree support p q) : d2958 p = d2958 q := by
  simp only [d2958, h 163 (by decide), agree12 p q h, agree2957 p q h]
theorem nonnegative2958 (p : Pattern) : 0 ≤ d2958 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2957 p)
def d2959 (p : Pattern) : Int := if p 162 then d2958 p else d2955 p
theorem agree2959 (p q : Pattern) (h : Agree support p q) : d2959 p = d2959 q := by
  simp only [d2959, h 162 (by decide), agree2958 p q h, agree2955 p q h]
theorem nonnegative2959 (p : Pattern) : 0 ≤ d2959 p :=
  nonnegative_ite (p 162) (nonnegative2958 p) (nonnegative2955 p)
def d2960 (p : Pattern) : Int := if p 161 then d2959 p else d2956 p
theorem agree2960 (p q : Pattern) (h : Agree support p q) : d2960 p = d2960 q := by
  simp only [d2960, h 161 (by decide), agree2959 p q h, agree2956 p q h]
theorem nonnegative2960 (p : Pattern) : 0 ≤ d2960 p :=
  nonnegative_ite (p 161) (nonnegative2959 p) (nonnegative2956 p)
def d2961 (p : Pattern) : Int := if p 182 then d1718 p else d2935 p
theorem agree2961 (p q : Pattern) (h : Agree support p q) : d2961 p = d2961 q := by
  simp only [d2961, h 182 (by decide), agree1718 p q h, agree2935 p q h]
theorem nonnegative2961 (p : Pattern) : 0 ≤ d2961 p :=
  nonnegative_ite (p 182) (nonnegative1718 p) (nonnegative2935 p)
def d2962 (p : Pattern) : Int := if p 204 then d1724 p else d35 p
theorem agree2962 (p q : Pattern) (h : Agree support p q) : d2962 p = d2962 q := by
  simp only [d2962, h 204 (by decide), agree1724 p q h, agree35 p q h]
theorem nonnegative2962 (p : Pattern) : 0 ≤ d2962 p :=
  nonnegative_ite (p 204) (nonnegative1724 p) (nonnegative35 p)
def d2963 (p : Pattern) : Int := if p 182 then d1725 p else d2962 p
theorem agree2963 (p q : Pattern) (h : Agree support p q) : d2963 p = d2963 q := by
  simp only [d2963, h 182 (by decide), agree1725 p q h, agree2962 p q h]
theorem nonnegative2963 (p : Pattern) : 0 ≤ d2963 p :=
  nonnegative_ite (p 182) (nonnegative1725 p) (nonnegative2962 p)
def d2964 (p : Pattern) : Int := if p 163 then d2963 p else d2961 p
theorem agree2964 (p q : Pattern) (h : Agree support p q) : d2964 p = d2964 q := by
  simp only [d2964, h 163 (by decide), agree2963 p q h, agree2961 p q h]
theorem nonnegative2964 (p : Pattern) : 0 ≤ d2964 p :=
  nonnegative_ite (p 163) (nonnegative2963 p) (nonnegative2961 p)
def d2965 (p : Pattern) : Int := if p 162 then d2932 p else d2964 p
theorem agree2965 (p q : Pattern) (h : Agree support p q) : d2965 p = d2965 q := by
  simp only [d2965, h 162 (by decide), agree2932 p q h, agree2964 p q h]
theorem nonnegative2965 (p : Pattern) : 0 ≤ d2965 p :=
  nonnegative_ite (p 162) (nonnegative2932 p) (nonnegative2964 p)
def d2966 (p : Pattern) : Int := if p 161 then d12 p else d2965 p
theorem agree2966 (p q : Pattern) (h : Agree support p q) : d2966 p = d2966 q := by
  simp only [d2966, h 161 (by decide), agree12 p q h, agree2965 p q h]
theorem nonnegative2966 (p : Pattern) : 0 ≤ d2966 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2965 p)
def d2967 (p : Pattern) : Int := if p 160 then d2966 p else d2960 p
theorem agree2967 (p q : Pattern) (h : Agree support p q) : d2967 p = d2967 q := by
  simp only [d2967, h 160 (by decide), agree2966 p q h, agree2960 p q h]
theorem nonnegative2967 (p : Pattern) : 0 ≤ d2967 p :=
  nonnegative_ite (p 160) (nonnegative2966 p) (nonnegative2960 p)
def d2968 (p : Pattern) : Int := if p 163 then d2961 p else d2951 p
theorem agree2968 (p q : Pattern) (h : Agree support p q) : d2968 p = d2968 q := by
  simp only [d2968, h 163 (by decide), agree2961 p q h, agree2951 p q h]
theorem nonnegative2968 (p : Pattern) : 0 ≤ d2968 p :=
  nonnegative_ite (p 163) (nonnegative2961 p) (nonnegative2951 p)
def d2969 (p : Pattern) : Int := if p 163 then d2957 p else d2954 p
theorem agree2969 (p q : Pattern) (h : Agree support p q) : d2969 p = d2969 q := by
  simp only [d2969, h 163 (by decide), agree2957 p q h, agree2954 p q h]
theorem nonnegative2969 (p : Pattern) : 0 ≤ d2969 p :=
  nonnegative_ite (p 163) (nonnegative2957 p) (nonnegative2954 p)
def d2970 (p : Pattern) : Int := if p 162 then d2969 p else d2968 p
theorem agree2970 (p q : Pattern) (h : Agree support p q) : d2970 p = d2970 q := by
  simp only [d2970, h 162 (by decide), agree2969 p q h, agree2968 p q h]
theorem nonnegative2970 (p : Pattern) : 0 ≤ d2970 p :=
  nonnegative_ite (p 162) (nonnegative2969 p) (nonnegative2968 p)
def d2971 (p : Pattern) : Int := if p 163 then d2928 p else d2954 p
theorem agree2971 (p q : Pattern) (h : Agree support p q) : d2971 p = d2971 q := by
  simp only [d2971, h 163 (by decide), agree2928 p q h, agree2954 p q h]
theorem nonnegative2971 (p : Pattern) : 0 ≤ d2971 p :=
  nonnegative_ite (p 163) (nonnegative2928 p) (nonnegative2954 p)
def d2972 (p : Pattern) : Int := if p 162 then d2932 p else d2971 p
theorem agree2972 (p q : Pattern) (h : Agree support p q) : d2972 p = d2972 q := by
  simp only [d2972, h 162 (by decide), agree2932 p q h, agree2971 p q h]
theorem nonnegative2972 (p : Pattern) : 0 ≤ d2972 p :=
  nonnegative_ite (p 162) (nonnegative2932 p) (nonnegative2971 p)
def d2973 (p : Pattern) : Int := if p 161 then d2972 p else d2970 p
theorem agree2973 (p q : Pattern) (h : Agree support p q) : d2973 p = d2973 q := by
  simp only [d2973, h 161 (by decide), agree2972 p q h, agree2970 p q h]
theorem nonnegative2973 (p : Pattern) : 0 ≤ d2973 p :=
  nonnegative_ite (p 161) (nonnegative2972 p) (nonnegative2970 p)
def d2974 (p : Pattern) : Int := if p 163 then d12 p else d2963 p
theorem agree2974 (p q : Pattern) (h : Agree support p q) : d2974 p = d2974 q := by
  simp only [d2974, h 163 (by decide), agree12 p q h, agree2963 p q h]
theorem nonnegative2974 (p : Pattern) : 0 ≤ d2974 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2963 p)
def d2975 (p : Pattern) : Int := if p 162 then d12 p else d2974 p
theorem agree2975 (p q : Pattern) (h : Agree support p q) : d2975 p = d2975 q := by
  simp only [d2975, h 162 (by decide), agree12 p q h, agree2974 p q h]
theorem nonnegative2975 (p : Pattern) : 0 ≤ d2975 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2974 p)
def d2976 (p : Pattern) : Int := if p 161 then d12 p else d2975 p
theorem agree2976 (p q : Pattern) (h : Agree support p q) : d2976 p = d2976 q := by
  simp only [d2976, h 161 (by decide), agree12 p q h, agree2975 p q h]
theorem nonnegative2976 (p : Pattern) : 0 ≤ d2976 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2975 p)
def d2977 (p : Pattern) : Int := if p 160 then d2976 p else d2973 p
theorem agree2977 (p q : Pattern) (h : Agree support p q) : d2977 p = d2977 q := by
  simp only [d2977, h 160 (by decide), agree2976 p q h, agree2973 p q h]
theorem nonnegative2977 (p : Pattern) : 0 ≤ d2977 p :=
  nonnegative_ite (p 160) (nonnegative2976 p) (nonnegative2973 p)
def d2978 (p : Pattern) : Int := if p 141 then d2977 p else d2967 p
theorem agree2978 (p q : Pattern) (h : Agree support p q) : d2978 p = d2978 q := by
  simp only [d2978, h 141 (by decide), agree2977 p q h, agree2967 p q h]
theorem nonnegative2978 (p : Pattern) : 0 ≤ d2978 p :=
  nonnegative_ite (p 141) (nonnegative2977 p) (nonnegative2967 p)
def d2979 (p : Pattern) : Int := if p 138 then d2978 p else d2947 p
theorem agree2979 (p q : Pattern) (h : Agree support p q) : d2979 p = d2979 q := by
  simp only [d2979, h 138 (by decide), agree2978 p q h, agree2947 p q h]
theorem nonnegative2979 (p : Pattern) : 0 ≤ d2979 p :=
  nonnegative_ite (p 138) (nonnegative2978 p) (nonnegative2947 p)
def d2980 (p : Pattern) : Int := if p 163 then d2931 p else d2957 p
theorem agree2980 (p q : Pattern) (h : Agree support p q) : d2980 p = d2980 q := by
  simp only [d2980, h 163 (by decide), agree2931 p q h, agree2957 p q h]
theorem nonnegative2980 (p : Pattern) : 0 ≤ d2980 p :=
  nonnegative_ite (p 163) (nonnegative2931 p) (nonnegative2957 p)
def d2981 (p : Pattern) : Int := if p 162 then d2932 p else d2980 p
theorem agree2981 (p q : Pattern) (h : Agree support p q) : d2981 p = d2981 q := by
  simp only [d2981, h 162 (by decide), agree2932 p q h, agree2980 p q h]
theorem nonnegative2981 (p : Pattern) : 0 ≤ d2981 p :=
  nonnegative_ite (p 162) (nonnegative2932 p) (nonnegative2980 p)
def d2982 (p : Pattern) : Int := if p 162 then d12 p else d2932 p
theorem agree2982 (p q : Pattern) (h : Agree support p q) : d2982 p = d2982 q := by
  simp only [d2982, h 162 (by decide), agree12 p q h, agree2932 p q h]
theorem nonnegative2982 (p : Pattern) : 0 ≤ d2982 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2932 p)
def d2983 (p : Pattern) : Int := if p 161 then d2982 p else d2981 p
theorem agree2983 (p q : Pattern) (h : Agree support p q) : d2983 p = d2983 q := by
  simp only [d2983, h 161 (by decide), agree2982 p q h, agree2981 p q h]
theorem nonnegative2983 (p : Pattern) : 0 ≤ d2983 p :=
  nonnegative_ite (p 161) (nonnegative2982 p) (nonnegative2981 p)
def d2984 (p : Pattern) : Int := if p 161 then d12 p else d2982 p
theorem agree2984 (p q : Pattern) (h : Agree support p q) : d2984 p = d2984 q := by
  simp only [d2984, h 161 (by decide), agree12 p q h, agree2982 p q h]
theorem nonnegative2984 (p : Pattern) : 0 ≤ d2984 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2982 p)
def d2985 (p : Pattern) : Int := if p 160 then d2984 p else d2983 p
theorem agree2985 (p q : Pattern) (h : Agree support p q) : d2985 p = d2985 q := by
  simp only [d2985, h 160 (by decide), agree2984 p q h, agree2983 p q h]
theorem nonnegative2985 (p : Pattern) : 0 ≤ d2985 p :=
  nonnegative_ite (p 160) (nonnegative2984 p) (nonnegative2983 p)
def d2986 (p : Pattern) : Int := if p 160 then d12 p else d2984 p
theorem agree2986 (p q : Pattern) (h : Agree support p q) : d2986 p = d2986 q := by
  simp only [d2986, h 160 (by decide), agree12 p q h, agree2984 p q h]
theorem nonnegative2986 (p : Pattern) : 0 ≤ d2986 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative2984 p)
def d2987 (p : Pattern) : Int := if p 141 then d2986 p else d2985 p
theorem agree2987 (p q : Pattern) (h : Agree support p q) : d2987 p = d2987 q := by
  simp only [d2987, h 141 (by decide), agree2986 p q h, agree2985 p q h]
theorem nonnegative2987 (p : Pattern) : 0 ≤ d2987 p :=
  nonnegative_ite (p 141) (nonnegative2986 p) (nonnegative2985 p)
def d2988 (p : Pattern) : Int := if p 138 then d2987 p else d2978 p
theorem agree2988 (p q : Pattern) (h : Agree support p q) : d2988 p = d2988 q := by
  simp only [d2988, h 138 (by decide), agree2987 p q h, agree2978 p q h]
theorem nonnegative2988 (p : Pattern) : 0 ≤ d2988 p :=
  nonnegative_ite (p 138) (nonnegative2987 p) (nonnegative2978 p)
def d2989 (p : Pattern) : Int := if p 116 then d2988 p else d2979 p
theorem agree2989 (p q : Pattern) (h : Agree support p q) : d2989 p = d2989 q := by
  simp only [d2989, h 116 (by decide), agree2988 p q h, agree2979 p q h]
theorem nonnegative2989 (p : Pattern) : 0 ≤ d2989 p :=
  nonnegative_ite (p 116) (nonnegative2988 p) (nonnegative2979 p)
def d2990 (p : Pattern) : Int := if p 138 then d12 p else d2978 p
theorem agree2990 (p q : Pattern) (h : Agree support p q) : d2990 p = d2990 q := by
  simp only [d2990, h 138 (by decide), agree12 p q h, agree2978 p q h]
theorem nonnegative2990 (p : Pattern) : 0 ≤ d2990 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative2978 p)
def d2991 (p : Pattern) : Int := if p 116 then d2990 p else d2979 p
theorem agree2991 (p q : Pattern) (h : Agree support p q) : d2991 p = d2991 q := by
  simp only [d2991, h 116 (by decide), agree2990 p q h, agree2979 p q h]
theorem nonnegative2991 (p : Pattern) : 0 ≤ d2991 p :=
  nonnegative_ite (p 116) (nonnegative2990 p) (nonnegative2979 p)
def d2992 (p : Pattern) : Int := if p 115 then d2991 p else d2989 p
theorem agree2992 (p q : Pattern) (h : Agree support p q) : d2992 p = d2992 q := by
  simp only [d2992, h 115 (by decide), agree2991 p q h, agree2989 p q h]
theorem nonnegative2992 (p : Pattern) : 0 ≤ d2992 p :=
  nonnegative_ite (p 115) (nonnegative2991 p) (nonnegative2989 p)
def d2993 (p : Pattern) : Int := if p 204 then d1942 p else d103 p
theorem agree2993 (p q : Pattern) (h : Agree support p q) : d2993 p = d2993 q := by
  simp only [d2993, h 204 (by decide), agree1942 p q h, agree103 p q h]
theorem nonnegative2993 (p : Pattern) : 0 ≤ d2993 p :=
  nonnegative_ite (p 204) (nonnegative1942 p) (nonnegative103 p)
def d2994 (p : Pattern) : Int := if p 182 then d1876 p else d2993 p
theorem agree2994 (p q : Pattern) (h : Agree support p q) : d2994 p = d2994 q := by
  simp only [d2994, h 182 (by decide), agree1876 p q h, agree2993 p q h]
theorem nonnegative2994 (p : Pattern) : 0 ≤ d2994 p :=
  nonnegative_ite (p 182) (nonnegative1876 p) (nonnegative2993 p)
def d2995 (p : Pattern) : Int := if p 204 then d2130 p else d107 p
theorem agree2995 (p q : Pattern) (h : Agree support p q) : d2995 p = d2995 q := by
  simp only [d2995, h 204 (by decide), agree2130 p q h, agree107 p q h]
theorem nonnegative2995 (p : Pattern) : 0 ≤ d2995 p :=
  nonnegative_ite (p 204) (nonnegative2130 p) (nonnegative107 p)
def d2996 (p : Pattern) : Int := if p 182 then d1884 p else d2995 p
theorem agree2996 (p q : Pattern) (h : Agree support p q) : d2996 p = d2996 q := by
  simp only [d2996, h 182 (by decide), agree1884 p q h, agree2995 p q h]
theorem nonnegative2996 (p : Pattern) : 0 ≤ d2996 p :=
  nonnegative_ite (p 182) (nonnegative1884 p) (nonnegative2995 p)
def d2997 (p : Pattern) : Int := if p 163 then d2996 p else d2994 p
theorem agree2997 (p q : Pattern) (h : Agree support p q) : d2997 p = d2997 q := by
  simp only [d2997, h 163 (by decide), agree2996 p q h, agree2994 p q h]
theorem nonnegative2997 (p : Pattern) : 0 ≤ d2997 p :=
  nonnegative_ite (p 163) (nonnegative2996 p) (nonnegative2994 p)
def d2998 (p : Pattern) : Int := if p 162 then d2997 p else d2994 p
theorem agree2998 (p q : Pattern) (h : Agree support p q) : d2998 p = d2998 q := by
  simp only [d2998, h 162 (by decide), agree2997 p q h, agree2994 p q h]
theorem nonnegative2998 (p : Pattern) : 0 ≤ d2998 p :=
  nonnegative_ite (p 162) (nonnegative2997 p) (nonnegative2994 p)
def d2999 (p : Pattern) : Int := if p 163 then d12 p else d2928 p
theorem agree2999 (p q : Pattern) (h : Agree support p q) : d2999 p = d2999 q := by
  simp only [d2999, h 163 (by decide), agree12 p q h, agree2928 p q h]
theorem nonnegative2999 (p : Pattern) : 0 ≤ d2999 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2928 p)
end NetHack.Sokoban22Refined85
