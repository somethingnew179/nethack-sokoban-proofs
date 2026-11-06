/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions106
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub12840 (p : Pattern) : d3004 (change p 10000 (some 204)) = d7087 p := by
  change (if p 182 then d1906 (change p 10000 (some 204)) else d3002 (change p 10000 (some 204))) = d7087 p
  rw [sub12839, sub12836]
  rfl
theorem sub12841 (p : Pattern) : d3005 (change p 10000 (some 204)) = d7087 p := by
  change (if p 163 then d3004 (change p 10000 (some 204)) else d3003 (change p 10000 (some 204))) = d7087 p
  rw [sub12840, sub12838]
  simp only [ite_self]
theorem sub12842 (p : Pattern) : d3006 (change p 10000 (some 204)) = d7087 p := by
  change (if p 182 then d12 (change p 10000 (some 204)) else d3002 (change p 10000 (some 204))) = d7087 p
  rw [sub12617, sub12836]
  rfl
theorem sub12843 (p : Pattern) : d1960 (change p 10000 (some 204)) = d1960 p := by
  change (if p 247 then d11 (change p 10000 (some 204)) else d5 (change p 10000 (some 204))) = d1960 p
  rw [sub12658, sub12806]
  rfl
theorem sub12844 (p : Pattern) : d1961 (change p 10000 (some 204)) = d1961 p := by
  change (if p 246 then d39 (change p 10000 (some 204)) else d1960 (change p 10000 (some 204))) = d1961 p
  rw [sub12711, sub12843]
  rfl
theorem sub12845 (p : Pattern) : d1962 (change p 10000 (some 204)) = d1962 p := by
  change (if p 225 then d1961 (change p 10000 (some 204)) else d107 (change p 10000 (some 204))) = d1962 p
  rw [sub12844, sub12815]
  rfl
theorem sub12846 (p : Pattern) : d348 (change p 10000 (some 204)) = d348 p := by
  change (if p 246 then d12 (change p 10000 (some 204)) else d106 (change p 10000 (some 204))) = d348 p
  rw [sub12617, sub12808]
  rfl
theorem sub12847 (p : Pattern) : d1965 (change p 10000 (some 204)) = d1965 p := by
  change (if p 225 then d348 (change p 10000 (some 204)) else d1964 (change p 10000 (some 204))) = d1965 p
  rw [sub12846, sub12817]
  rfl
theorem sub12848 (p : Pattern) : d1966 (change p 10000 (some 204)) = d1966 p := by
  change (if p 224 then d1965 (change p 10000 (some 204)) else d1962 (change p 10000 (some 204))) = d1966 p
  rw [sub12847, sub12845]
  rfl
theorem sub12849 (p : Pattern) : d3007 (change p 10000 (some 204)) = d1966 p := by
  change d1966 (change p 10000 (some 204)) = d1966 p
  exact sub12848 p
theorem sub12850 (p : Pattern) : d3008 (change p 10000 (some 204)) = d7088 p := by
  change (if p 182 then d12 (change p 10000 (some 204)) else d3007 (change p 10000 (some 204))) = d7088 p
  rw [sub12617, sub12849]
  rfl
theorem sub12851 (p : Pattern) : d3009 (change p 10000 (some 204)) = d7089 p := by
  change (if p 163 then d3008 (change p 10000 (some 204)) else d3006 (change p 10000 (some 204))) = d7089 p
  rw [sub12850, sub12842]
  rfl
theorem sub12852 (p : Pattern) : d3010 (change p 10000 (some 204)) = d7090 p := by
  change (if p 162 then d3009 (change p 10000 (some 204)) else d3005 (change p 10000 (some 204))) = d7090 p
  rw [sub12851, sub12841]
  rfl
theorem sub12853 (p : Pattern) : d3011 (change p 10000 (some 204)) = d7084 p := by
  change (if p 163 then d12 (change p 10000 (some 204)) else d2940 (change p 10000 (some 204))) = d7084 p
  rw [sub12617, sub12732]
  rfl
theorem sub12854 (p : Pattern) : d3012 (change p 10000 (some 204)) = d7091 p := by
  change (if p 162 then d3011 (change p 10000 (some 204)) else d3009 (change p 10000 (some 204))) = d7091 p
  rw [sub12853, sub12851]
  rfl
theorem sub12855 (p : Pattern) : d3013 (change p 10000 (some 204)) = d7092 p := by
  change (if p 161 then d3012 (change p 10000 (some 204)) else d3010 (change p 10000 (some 204))) = d7092 p
  rw [sub12854, sub12852]
  rfl
theorem sub12856 (p : Pattern) : d3014 (change p 10000 (some 204)) = d7093 p := by
  change (if p 160 then d3013 (change p 10000 (some 204)) else d3001 (change p 10000 (some 204))) = d7093 p
  rw [sub12855, sub12827]
  rfl
theorem sub12857 (p : Pattern) : d3 (change p 10000 (some 204)) = d3 p := by
  rfl
theorem sub12858 (p : Pattern) : d115 (change p 10000 (some 204)) = d115 p := by
  change (if p 247 then d12 (change p 10000 (some 204)) else d3 (change p 10000 (some 204))) = d115 p
  rw [sub12617, sub12857]
  rfl
theorem sub12859 (p : Pattern) : d116 (change p 10000 (some 204)) = d116 p := by
  change (if p 246 then d115 (change p 10000 (some 204)) else d3 (change p 10000 (some 204))) = d116 p
  rw [sub12858, sub12857]
  rfl
theorem sub12860 (p : Pattern) : d1894 (change p 10000 (some 204)) = d1894 p := by
  change (if p 247 then d7 (change p 10000 (some 204)) else d3 (change p 10000 (some 204))) = d1894 p
  rw [sub12828, sub12857]
  rfl
theorem sub12861 (p : Pattern) : d1895 (change p 10000 (some 204)) = d1895 p := by
  change (if p 246 then d119 (change p 10000 (some 204)) else d1894 (change p 10000 (some 204))) = d1895 p
  rw [sub12830, sub12860]
  rfl
theorem sub12862 (p : Pattern) : d2124 (change p 10000 (some 204)) = d2124 p := by
  change (if p 225 then d1895 (change p 10000 (some 204)) else d116 (change p 10000 (some 204))) = d2124 p
  rw [sub12861, sub12859]
  rfl
theorem sub12863 (p : Pattern) : d2125 (change p 10000 (some 204)) = d2125 p := by
  change (if p 224 then d1895 (change p 10000 (some 204)) else d2124 (change p 10000 (some 204))) = d2125 p
  rw [sub12861, sub12862]
  rfl
theorem sub12864 (p : Pattern) : d3015 (change p 10000 (some 204)) = d2125 p := by
  change d2125 (change p 10000 (some 204)) = d2125 p
  exact sub12863 p
theorem sub12865 (p : Pattern) : d1922 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12866 (p : Pattern) : d3016 (change p 10000 (some 204)) = d7094 p := by
  change (if p 182 then d1922 (change p 10000 (some 204)) else d3015 (change p 10000 (some 204))) = d7094 p
  rw [sub12865, sub12864]
  rfl
theorem sub12867 (p : Pattern) : d3017 (change p 10000 (some 204)) = d7095 p := by
  change (if p 163 then d3016 (change p 10000 (some 204)) else d2994 (change p 10000 (some 204))) = d7095 p
  rw [sub12866, sub12814]
  rfl
theorem sub12868 (p : Pattern) : d3018 (change p 10000 (some 204)) = d7096 p := by
  change (if p 163 then d2928 (change p 10000 (some 204)) else d2996 (change p 10000 (some 204))) = d7096 p
  rw [sub12709, sub12822]
  rfl
theorem sub12869 (p : Pattern) : d3019 (change p 10000 (some 204)) = d7097 p := by
  change (if p 162 then d3018 (change p 10000 (some 204)) else d3017 (change p 10000 (some 204))) = d7097 p
  rw [sub12868, sub12867]
  rfl
theorem sub12870 (p : Pattern) : d3020 (change p 10000 (some 204)) = d7098 p := by
  change (if p 163 then d2931 (change p 10000 (some 204)) else d2996 (change p 10000 (some 204))) = d7098 p
  rw [sub12717, sub12822]
  rfl
theorem sub12871 (p : Pattern) : d3021 (change p 10000 (some 204)) = d7099 p := by
  change (if p 162 then d12 (change p 10000 (some 204)) else d3020 (change p 10000 (some 204))) = d7099 p
  rw [sub12617, sub12870]
  rfl
theorem sub12872 (p : Pattern) : d3022 (change p 10000 (some 204)) = d7100 p := by
  change (if p 161 then d3021 (change p 10000 (some 204)) else d3019 (change p 10000 (some 204))) = d7100 p
  rw [sub12871, sub12869]
  rfl
theorem sub12873 (p : Pattern) : d1891 (change p 10000 (some 204)) = d1891 p := by
  change (if p 247 then d9 (change p 10000 (some 204)) else d3 (change p 10000 (some 204))) = d1891 p
  rw [sub12641, sub12857]
  rfl
theorem sub12874 (p : Pattern) : d1892 (change p 10000 (some 204)) = d1892 p := by
  change (if p 246 then d23 (change p 10000 (some 204)) else d1891 (change p 10000 (some 204))) = d1892 p
  rw [sub12642, sub12873]
  rfl
theorem sub12875 (p : Pattern) : d1893 (change p 10000 (some 204)) = d1893 p := by
  change (if p 225 then d1892 (change p 10000 (some 204)) else d116 (change p 10000 (some 204))) = d1893 p
  rw [sub12874, sub12859]
  rfl
theorem sub12876 (p : Pattern) : d1896 (change p 10000 (some 204)) = d1896 p := by
  change (if p 246 then d12 (change p 10000 (some 204)) else d115 (change p 10000 (some 204))) = d1896 p
  rw [sub12617, sub12858]
  rfl
theorem sub12877 (p : Pattern) : d1897 (change p 10000 (some 204)) = d1897 p := by
  change (if p 225 then d1896 (change p 10000 (some 204)) else d1895 (change p 10000 (some 204))) = d1897 p
  rw [sub12876, sub12861]
  rfl
theorem sub12878 (p : Pattern) : d1898 (change p 10000 (some 204)) = d1898 p := by
  change (if p 224 then d1897 (change p 10000 (some 204)) else d1893 (change p 10000 (some 204))) = d1898 p
  rw [sub12877, sub12875]
  rfl
theorem sub12879 (p : Pattern) : d3023 (change p 10000 (some 204)) = d1898 p := by
  change d1898 (change p 10000 (some 204)) = d1898 p
  exact sub12878 p
theorem sub12880 (p : Pattern) : d3024 (change p 10000 (some 204)) = d7101 p := by
  change (if p 182 then d12 (change p 10000 (some 204)) else d3023 (change p 10000 (some 204))) = d7101 p
  rw [sub12617, sub12879]
  rfl
theorem sub12881 (p : Pattern) : d3025 (change p 10000 (some 204)) = d7102 p := by
  change (if p 163 then d3024 (change p 10000 (some 204)) else d3004 (change p 10000 (some 204))) = d7102 p
  rw [sub12880, sub12840]
  rfl
theorem sub12882 (p : Pattern) : d3026 (change p 10000 (some 204)) = d7103 p := by
  change (if p 163 then d2940 (change p 10000 (some 204)) else d3008 (change p 10000 (some 204))) = d7103 p
  rw [sub12732, sub12850]
  rfl
theorem sub12883 (p : Pattern) : d3027 (change p 10000 (some 204)) = d7104 p := by
  change (if p 162 then d3026 (change p 10000 (some 204)) else d3025 (change p 10000 (some 204))) = d7104 p
  rw [sub12882, sub12881]
  rfl
theorem sub12884 (p : Pattern) : d3028 (change p 10000 (some 204)) = d7105 p := by
  change (if p 163 then d2942 (change p 10000 (some 204)) else d3008 (change p 10000 (some 204))) = d7105 p
  rw [sub12734, sub12850]
  rfl
theorem sub12885 (p : Pattern) : d3029 (change p 10000 (some 204)) = d7106 p := by
  change (if p 162 then d12 (change p 10000 (some 204)) else d3028 (change p 10000 (some 204))) = d7106 p
  rw [sub12617, sub12884]
  rfl
theorem sub12886 (p : Pattern) : d3030 (change p 10000 (some 204)) = d7107 p := by
  change (if p 161 then d3029 (change p 10000 (some 204)) else d3027 (change p 10000 (some 204))) = d7107 p
  rw [sub12885, sub12883]
  rfl
theorem sub12887 (p : Pattern) : d3031 (change p 10000 (some 204)) = d7108 p := by
  change (if p 160 then d3030 (change p 10000 (some 204)) else d3022 (change p 10000 (some 204))) = d7108 p
  rw [sub12886, sub12872]
  rfl
theorem sub12888 (p : Pattern) : d3032 (change p 10000 (some 204)) = d7109 p := by
  change (if p 141 then d3031 (change p 10000 (some 204)) else d3014 (change p 10000 (some 204))) = d7109 p
  rw [sub12887, sub12856]
  rfl
theorem sub12889 (p : Pattern) : d2107 (change p 10000 (some 204)) = d2107 p := by
  change (if p 225 then d1946 (change p 10000 (some 204)) else d1940 (change p 10000 (some 204))) = d2107 p
  rw [sub12831, sub12809]
  rfl
theorem sub12890 (p : Pattern) : d2108 (change p 10000 (some 204)) = d2108 p := by
  change (if p 224 then d2107 (change p 10000 (some 204)) else d1947 (change p 10000 (some 204))) = d2108 p
  rw [sub12889, sub12832]
  rfl
theorem sub12891 (p : Pattern) : d3033 (change p 10000 (some 204)) = d2108 p := by
  change d2108 (change p 10000 (some 204)) = d2108 p
  exact sub12890 p
theorem sub12892 (p : Pattern) : d1943 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12893 (p : Pattern) : d3034 (change p 10000 (some 204)) = d7110 p := by
  change (if p 182 then d1943 (change p 10000 (some 204)) else d3033 (change p 10000 (some 204))) = d7110 p
  rw [sub12892, sub12891]
  rfl
theorem sub12894 (p : Pattern) : d3035 (change p 10000 (some 204)) = d3035 p := by
  change (if p 247 then d11 (change p 10000 (some 204)) else d1 (change p 10000 (some 204))) = d3035 p
  rw [sub12658, sub12803]
  rfl
theorem sub12895 (p : Pattern) : d3036 (change p 10000 (some 204)) = d3036 p := by
  change (if p 246 then d57 (change p 10000 (some 204)) else d3035 (change p 10000 (some 204))) = d3036 p
  rw [sub12673, sub12894]
  rfl
theorem sub12896 (p : Pattern) : d3037 (change p 10000 (some 204)) = d3037 p := by
  change (if p 225 then d3036 (change p 10000 (some 204)) else d1940 (change p 10000 (some 204))) = d3037 p
  rw [sub12895, sub12809]
  rfl
theorem sub12897 (p : Pattern) : d3038 (change p 10000 (some 204)) = d3038 p := by
  change (if p 224 then d3037 (change p 10000 (some 204)) else d1947 (change p 10000 (some 204))) = d3038 p
  rw [sub12896, sub12832]
  rfl
theorem sub12898 (p : Pattern) : d3039 (change p 10000 (some 204)) = d3038 p := by
  change d3038 (change p 10000 (some 204)) = d3038 p
  exact sub12897 p
theorem sub12899 (p : Pattern) : d1952 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12900 (p : Pattern) : d3040 (change p 10000 (some 204)) = d7111 p := by
  change (if p 182 then d1952 (change p 10000 (some 204)) else d3039 (change p 10000 (some 204))) = d7111 p
  rw [sub12899, sub12898]
  rfl
theorem sub12901 (p : Pattern) : d3041 (change p 10000 (some 204)) = d7112 p := by
  change (if p 163 then d3040 (change p 10000 (some 204)) else d3034 (change p 10000 (some 204))) = d7112 p
  rw [sub12900, sub12893]
  rfl
theorem sub12902 (p : Pattern) : d1958 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12903 (p : Pattern) : d3042 (change p 10000 (some 204)) = d7087 p := by
  change (if p 182 then d1958 (change p 10000 (some 204)) else d3002 (change p 10000 (some 204))) = d7087 p
  rw [sub12902, sub12836]
  rfl
theorem sub12904 (p : Pattern) : d1967 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12905 (p : Pattern) : d3043 (change p 10000 (some 204)) = d7088 p := by
  change (if p 182 then d1967 (change p 10000 (some 204)) else d3007 (change p 10000 (some 204))) = d7088 p
  rw [sub12904, sub12849]
  rfl
theorem sub12906 (p : Pattern) : d3044 (change p 10000 (some 204)) = d7089 p := by
  change (if p 163 then d3043 (change p 10000 (some 204)) else d3042 (change p 10000 (some 204))) = d7089 p
  rw [sub12905, sub12903]
  rfl
theorem sub12907 (p : Pattern) : d3045 (change p 10000 (some 204)) = d7113 p := by
  change (if p 162 then d3044 (change p 10000 (some 204)) else d3041 (change p 10000 (some 204))) = d7113 p
  rw [sub12906, sub12901]
  rfl
theorem sub12908 (p : Pattern) : d3046 (change p 10000 (some 204)) = d7091 p := by
  change (if p 162 then d2999 (change p 10000 (some 204)) else d3044 (change p 10000 (some 204))) = d7091 p
  rw [sub12825, sub12906]
  rfl
theorem sub12909 (p : Pattern) : d3047 (change p 10000 (some 204)) = d7114 p := by
  change (if p 161 then d3046 (change p 10000 (some 204)) else d3045 (change p 10000 (some 204))) = d7114 p
  rw [sub12908, sub12907]
  rfl
theorem sub12910 (p : Pattern) : d3048 (change p 10000 (some 204)) = d7101 p := by
  change (if p 182 then d1899 (change p 10000 (some 204)) else d3023 (change p 10000 (some 204))) = d7101 p
  rw [sub12837, sub12879]
  rfl
theorem sub12911 (p : Pattern) : d120 (change p 10000 (some 204)) = d120 p := by
  change (if p 246 then d119 (change p 10000 (some 204)) else d7 (change p 10000 (some 204))) = d120 p
  rw [sub12830, sub12828]
  rfl
theorem sub12912 (p : Pattern) : d317 (change p 10000 (some 204)) = d317 p := by
  change (if p 246 then d12 (change p 10000 (some 204)) else d119 (change p 10000 (some 204))) = d317 p
  rw [sub12617, sub12830]
  rfl
theorem sub12913 (p : Pattern) : d1901 (change p 10000 (some 204)) = d1901 p := by
  change (if p 225 then d317 (change p 10000 (some 204)) else d120 (change p 10000 (some 204))) = d1901 p
  rw [sub12912, sub12911]
  rfl
theorem sub12914 (p : Pattern) : d1902 (change p 10000 (some 204)) = d1902 p := by
  change (if p 247 then d11 (change p 10000 (some 204)) else d7 (change p 10000 (some 204))) = d1902 p
  rw [sub12658, sub12828]
  rfl
theorem sub12915 (p : Pattern) : d1903 (change p 10000 (some 204)) = d1903 p := by
  change (if p 246 then d39 (change p 10000 (some 204)) else d1902 (change p 10000 (some 204))) = d1903 p
  rw [sub12711, sub12914]
  rfl
theorem sub12916 (p : Pattern) : d1904 (change p 10000 (some 204)) = d1904 p := by
  change (if p 225 then d317 (change p 10000 (some 204)) else d1903 (change p 10000 (some 204))) = d1904 p
  rw [sub12912, sub12915]
  rfl
theorem sub12917 (p : Pattern) : d1905 (change p 10000 (some 204)) = d1905 p := by
  change (if p 224 then d1904 (change p 10000 (some 204)) else d1901 (change p 10000 (some 204))) = d1905 p
  rw [sub12916, sub12913]
  rfl
theorem sub12918 (p : Pattern) : d3049 (change p 10000 (some 204)) = d1905 p := by
  change d1905 (change p 10000 (some 204)) = d1905 p
  exact sub12917 p
theorem sub12919 (p : Pattern) : d3050 (change p 10000 (some 204)) = d7115 p := by
  change (if p 182 then d1906 (change p 10000 (some 204)) else d3049 (change p 10000 (some 204))) = d7115 p
  rw [sub12839, sub12918]
  rfl
theorem sub12920 (p : Pattern) : d3051 (change p 10000 (some 204)) = d7116 p := by
  change (if p 163 then d3050 (change p 10000 (some 204)) else d3048 (change p 10000 (some 204))) = d7116 p
  rw [sub12919, sub12910]
  rfl
theorem sub12921 (p : Pattern) : d3052 (change p 10000 (some 204)) = d7117 p := by
  change (if p 162 then d12 (change p 10000 (some 204)) else d3051 (change p 10000 (some 204))) = d7117 p
  rw [sub12617, sub12920]
  rfl
theorem sub12922 (p : Pattern) : d3053 (change p 10000 (some 204)) = d7118 p := by
  change (if p 161 then d12 (change p 10000 (some 204)) else d3052 (change p 10000 (some 204))) = d7118 p
  rw [sub12617, sub12921]
  rfl
theorem sub12923 (p : Pattern) : d3054 (change p 10000 (some 204)) = d7119 p := by
  change (if p 160 then d3053 (change p 10000 (some 204)) else d3047 (change p 10000 (some 204))) = d7119 p
  rw [sub12922, sub12909]
  rfl
theorem sub12924 (p : Pattern) : d3055 (change p 10000 (some 204)) = d7120 p := by
  change (if p 163 then d3048 (change p 10000 (some 204)) else d3040 (change p 10000 (some 204))) = d7120 p
  rw [sub12910, sub12900]
  rfl
theorem sub12925 (p : Pattern) : d3056 (change p 10000 (some 204)) = d7103 p := by
  change (if p 163 then d2928 (change p 10000 (some 204)) else d3043 (change p 10000 (some 204))) = d7103 p
  rw [sub12709, sub12905]
  rfl
theorem sub12926 (p : Pattern) : d3057 (change p 10000 (some 204)) = d7121 p := by
  change (if p 162 then d3056 (change p 10000 (some 204)) else d3055 (change p 10000 (some 204))) = d7121 p
  rw [sub12925, sub12924]
  rfl
theorem sub12927 (p : Pattern) : d3058 (change p 10000 (some 204)) = d7105 p := by
  change (if p 163 then d2931 (change p 10000 (some 204)) else d3043 (change p 10000 (some 204))) = d7105 p
  rw [sub12717, sub12905]
  rfl
theorem sub12928 (p : Pattern) : d3059 (change p 10000 (some 204)) = d7106 p := by
  change (if p 162 then d12 (change p 10000 (some 204)) else d3058 (change p 10000 (some 204))) = d7106 p
  rw [sub12617, sub12927]
  rfl
theorem sub12929 (p : Pattern) : d3060 (change p 10000 (some 204)) = d7122 p := by
  change (if p 161 then d3059 (change p 10000 (some 204)) else d3057 (change p 10000 (some 204))) = d7122 p
  rw [sub12928, sub12926]
  rfl
theorem sub12930 (p : Pattern) : d3061 (change p 10000 (some 204)) = d7123 p := by
  change (if p 163 then d12 (change p 10000 (some 204)) else d3050 (change p 10000 (some 204))) = d7123 p
  rw [sub12617, sub12919]
  rfl
theorem sub12931 (p : Pattern) : d3062 (change p 10000 (some 204)) = d7124 p := by
  change (if p 162 then d12 (change p 10000 (some 204)) else d3061 (change p 10000 (some 204))) = d7124 p
  rw [sub12617, sub12930]
  rfl
theorem sub12932 (p : Pattern) : d3063 (change p 10000 (some 204)) = d7125 p := by
  change (if p 161 then d12 (change p 10000 (some 204)) else d3062 (change p 10000 (some 204))) = d7125 p
  rw [sub12617, sub12931]
  rfl
theorem sub12933 (p : Pattern) : d3064 (change p 10000 (some 204)) = d7126 p := by
  change (if p 160 then d3063 (change p 10000 (some 204)) else d3060 (change p 10000 (some 204))) = d7126 p
  rw [sub12932, sub12929]
  rfl
theorem sub12934 (p : Pattern) : d3065 (change p 10000 (some 204)) = d7127 p := by
  change (if p 141 then d3064 (change p 10000 (some 204)) else d3054 (change p 10000 (some 204))) = d7127 p
  rw [sub12933, sub12923]
  rfl
theorem sub12935 (p : Pattern) : d3066 (change p 10000 (some 204)) = d7128 p := by
  change (if p 138 then d3065 (change p 10000 (some 204)) else d3032 (change p 10000 (some 204))) = d7128 p
  rw [sub12934, sub12888]
  rfl
theorem sub12936 (p : Pattern) : d3067 (change p 10000 (some 204)) = d7129 p := by
  change (if p 162 then d12 (change p 10000 (some 204)) else d2999 (change p 10000 (some 204))) = d7129 p
  rw [sub12617, sub12825]
  rfl
theorem sub12937 (p : Pattern) : d3068 (change p 10000 (some 204)) = d7130 p := by
  change (if p 161 then d12 (change p 10000 (some 204)) else d3067 (change p 10000 (some 204))) = d7130 p
  rw [sub12617, sub12936]
  rfl
theorem sub12938 (p : Pattern) : d3069 (change p 10000 (some 204)) = d7131 p := by
  change (if p 160 then d12 (change p 10000 (some 204)) else d3068 (change p 10000 (some 204))) = d7131 p
  rw [sub12617, sub12937]
  rfl
theorem sub12939 (p : Pattern) : d3070 (change p 10000 (some 204)) = d7132 p := by
  change (if p 141 then d12 (change p 10000 (some 204)) else d3069 (change p 10000 (some 204))) = d7132 p
  rw [sub12617, sub12938]
  rfl
theorem sub12940 (p : Pattern) : d3071 (change p 10000 (some 204)) = d7133 p := by
  change (if p 138 then d3070 (change p 10000 (some 204)) else d3065 (change p 10000 (some 204))) = d7133 p
  rw [sub12939, sub12934]
  rfl
theorem sub12941 (p : Pattern) : d3072 (change p 10000 (some 204)) = d7134 p := by
  change (if p 116 then d3071 (change p 10000 (some 204)) else d3066 (change p 10000 (some 204))) = d7134 p
  rw [sub12940, sub12935]
  rfl
theorem sub12942 (p : Pattern) : d3073 (change p 10000 (some 204)) = d7135 p := by
  change (if p 138 then d12 (change p 10000 (some 204)) else d3065 (change p 10000 (some 204))) = d7135 p
  rw [sub12617, sub12934]
  rfl
theorem sub12943 (p : Pattern) : d3074 (change p 10000 (some 204)) = d7136 p := by
  change (if p 116 then d3073 (change p 10000 (some 204)) else d3066 (change p 10000 (some 204))) = d7136 p
  rw [sub12942, sub12935]
  rfl
theorem sub12944 (p : Pattern) : d3075 (change p 10000 (some 204)) = d7137 p := by
  change (if p 115 then d3074 (change p 10000 (some 204)) else d3072 (change p 10000 (some 204))) = d7137 p
  rw [sub12943, sub12941]
  rfl
theorem sub12945 (p : Pattern) : d3076 (change p 10000 (some 204)) = d7138 p := by
  change (if p 71 then d3075 (change p 10000 (some 204)) else d2992 (change p 10000 (some 204))) = d7138 p
  rw [sub12944, sub12802]
  rfl
theorem sub12946 (p : Pattern) : d3077 (change p 10000 (some 204)) = d7139 p := by
  change (if p 49 then d3076 (change p 10000 (some 204)) else d2992 (change p 10000 (some 204))) = d7139 p
  rw [sub12945, sub12802]
  rfl
theorem sub12947 (p : Pattern) : d3078 (change p 10000 (some 204)) = d3078 p := by
  change (if p 225 then d1792 (change p 10000 (some 204)) else d1795 (change p 10000 (some 204))) = d3078 p
  rw [sub12674, sub12633]
  rfl
theorem sub12948 (p : Pattern) : d3079 (change p 10000 (some 204)) = d3079 p := by
  change (if p 224 then d3078 (change p 10000 (some 204)) else d1793 (change p 10000 (some 204))) = d3079 p
  rw [sub12947, sub12675]
  rfl
theorem sub12949 (p : Pattern) : d3080 (change p 10000 (some 204)) = d3079 p := by
  change d3079 (change p 10000 (some 204)) = d3079 p
  exact sub12948 p
theorem sub12950 (p : Pattern) : d2013 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12951 (p : Pattern) : d3081 (change p 10000 (some 204)) = d7140 p := by
  change (if p 182 then d2013 (change p 10000 (some 204)) else d3080 (change p 10000 (some 204))) = d7140 p
  rw [sub12950, sub12949]
  rfl
theorem sub12952 (p : Pattern) : d3082 (change p 10000 (some 204)) = d7141 p := by
  change (if p 163 then d3081 (change p 10000 (some 204)) else d2949 (change p 10000 (some 204))) = d7141 p
  rw [sub12951, sub12744]
  rfl
theorem sub12953 (p : Pattern) : d3083 (change p 10000 (some 204)) = d7142 p := by
  change (if p 162 then d3082 (change p 10000 (some 204)) else d2949 (change p 10000 (some 204))) = d7142 p
  rw [sub12952, sub12744]
  rfl
theorem sub12954 (p : Pattern) : d3084 (change p 10000 (some 204)) = d7143 p := by
  change (if p 162 then d2958 (change p 10000 (some 204)) else d3082 (change p 10000 (some 204))) = d7143 p
  rw [sub12761, sub12952]
  rfl
theorem sub12955 (p : Pattern) : d3085 (change p 10000 (some 204)) = d7144 p := by
  change (if p 161 then d3084 (change p 10000 (some 204)) else d3083 (change p 10000 (some 204))) = d7144 p
  rw [sub12954, sub12953]
  rfl
theorem sub12956 (p : Pattern) : d3086 (change p 10000 (some 204)) = d7039 p := by
  change (if p 182 then d1725 (change p 10000 (some 204)) else d2935 (change p 10000 (some 204))) = d7039 p
  rw [sub12666, sub12727]
  rfl
theorem sub12957 (p : Pattern) : d3087 (change p 10000 (some 204)) = d7039 p := by
  change (if p 163 then d3086 (change p 10000 (some 204)) else d2961 (change p 10000 (some 204))) = d7039 p
  rw [sub12956, sub12764]
  simp only [ite_self]
theorem sub12958 (p : Pattern) : d3088 (change p 10000 (some 204)) = d7039 p := by
  change (if p 182 then d1730 (change p 10000 (some 204)) else d2935 (change p 10000 (some 204))) = d7039 p
  rw [sub12669, sub12727]
  rfl
theorem sub12959 (p : Pattern) : d3089 (change p 10000 (some 204)) = d7053 p := by
  change (if p 182 then d12 (change p 10000 (some 204)) else d2962 (change p 10000 (some 204))) = d7053 p
  rw [sub12617, sub12772]
  rfl
end NetHack.Sokoban22Refined85
