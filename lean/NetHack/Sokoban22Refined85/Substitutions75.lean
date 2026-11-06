/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions74
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub9000 (p : Pattern) : d3024 (change p 10000 none) = d3024 p := by
  change (if p 182 then d12 (change p 10000 none) else d3023 (change p 10000 none)) = d3024 p
  rw [sub1, sub8999]
  rfl
theorem sub9001 (p : Pattern) : d3025 (change p 10000 none) = d3025 p := by
  change (if p 163 then d3024 (change p 10000 none) else d3004 (change p 10000 none)) = d3025 p
  rw [sub9000, sub8967]
  rfl
theorem sub9002 (p : Pattern) : d3026 (change p 10000 none) = d3026 p := by
  change (if p 163 then d2940 (change p 10000 none) else d3008 (change p 10000 none)) = d3026 p
  rw [sub8848, sub8977]
  rfl
theorem sub9003 (p : Pattern) : d3027 (change p 10000 none) = d3027 p := by
  change (if p 162 then d3026 (change p 10000 none) else d3025 (change p 10000 none)) = d3027 p
  rw [sub9002, sub9001]
  rfl
theorem sub9004 (p : Pattern) : d3028 (change p 10000 none) = d3028 p := by
  change (if p 163 then d2942 (change p 10000 none) else d3008 (change p 10000 none)) = d3028 p
  rw [sub8850, sub8977]
  rfl
theorem sub9005 (p : Pattern) : d3029 (change p 10000 none) = d3029 p := by
  change (if p 162 then d12 (change p 10000 none) else d3028 (change p 10000 none)) = d3029 p
  rw [sub1, sub9004]
  rfl
theorem sub9006 (p : Pattern) : d3030 (change p 10000 none) = d3030 p := by
  change (if p 161 then d3029 (change p 10000 none) else d3027 (change p 10000 none)) = d3030 p
  rw [sub9005, sub9003]
  rfl
theorem sub9007 (p : Pattern) : d3031 (change p 10000 none) = d3031 p := by
  change (if p 160 then d3030 (change p 10000 none) else d3022 (change p 10000 none)) = d3031 p
  rw [sub9006, sub8998]
  rfl
theorem sub9008 (p : Pattern) : d3032 (change p 10000 none) = d3032 p := by
  change (if p 141 then d3031 (change p 10000 none) else d3014 (change p 10000 none)) = d3032 p
  rw [sub9007, sub8983]
  rfl
theorem sub9009 (p : Pattern) : d2107 (change p 10000 none) = d2107 p := by
  change (if p 225 then d1946 (change p 10000 none) else d1940 (change p 10000 none)) = d2107 p
  rw [sub8944, sub8917]
  rfl
theorem sub9010 (p : Pattern) : d2108 (change p 10000 none) = d2108 p := by
  change (if p 224 then d2107 (change p 10000 none) else d1947 (change p 10000 none)) = d2108 p
  rw [sub9009, sub8945]
  rfl
theorem sub9011 (p : Pattern) : d3033 (change p 10000 none) = d3033 p := by
  change (if p 204 then d2108 (change p 10000 none) else d103 (change p 10000 none)) = d3033 p
  rw [sub9010, sub99]
  rfl
theorem sub9012 (p : Pattern) : d1943 (change p 10000 none) = d1943 p := by
  change (if p 204 then d12 (change p 10000 none) else d1942 (change p 10000 none)) = d1943 p
  rw [sub1, sub8919]
  rfl
theorem sub9013 (p : Pattern) : d3034 (change p 10000 none) = d3034 p := by
  change (if p 182 then d1943 (change p 10000 none) else d3033 (change p 10000 none)) = d3034 p
  rw [sub9012, sub9011]
  rfl
theorem sub9014 (p : Pattern) : d3035 (change p 10000 none) = d3035 p := by
  change (if p 247 then d11 (change p 10000 none) else d1 (change p 10000 none)) = d3035 p
  rw [sub32, sub97]
  rfl
theorem sub9015 (p : Pattern) : d3036 (change p 10000 none) = d3036 p := by
  change (if p 246 then d57 (change p 10000 none) else d3035 (change p 10000 none)) = d3036 p
  rw [sub52, sub9014]
  rfl
theorem sub9016 (p : Pattern) : d3037 (change p 10000 none) = d3037 p := by
  change (if p 225 then d3036 (change p 10000 none) else d1940 (change p 10000 none)) = d3037 p
  rw [sub9015, sub8917]
  rfl
theorem sub9017 (p : Pattern) : d3038 (change p 10000 none) = d3038 p := by
  change (if p 224 then d3037 (change p 10000 none) else d1947 (change p 10000 none)) = d3038 p
  rw [sub9016, sub8945]
  rfl
theorem sub9018 (p : Pattern) : d3039 (change p 10000 none) = d3039 p := by
  change (if p 204 then d3038 (change p 10000 none) else d103 (change p 10000 none)) = d3039 p
  rw [sub9017, sub99]
  rfl
theorem sub9019 (p : Pattern) : d1948 (change p 10000 none) = d1948 p := by
  change (if p 247 then d9 (change p 10000 none) else d1 (change p 10000 none)) = d1948 p
  rw [sub13, sub97]
  rfl
theorem sub9020 (p : Pattern) : d1949 (change p 10000 none) = d1949 p := by
  change (if p 246 then d23 (change p 10000 none) else d1948 (change p 10000 none)) = d1949 p
  rw [sub14, sub9019]
  rfl
theorem sub9021 (p : Pattern) : d1950 (change p 10000 none) = d1950 p := by
  change (if p 225 then d1949 (change p 10000 none) else d1940 (change p 10000 none)) = d1950 p
  rw [sub9020, sub8917]
  rfl
theorem sub9022 (p : Pattern) : d1951 (change p 10000 none) = d1951 p := by
  change (if p 224 then d1950 (change p 10000 none) else d1947 (change p 10000 none)) = d1951 p
  rw [sub9021, sub8945]
  rfl
theorem sub9023 (p : Pattern) : d1952 (change p 10000 none) = d1952 p := by
  change (if p 204 then d12 (change p 10000 none) else d1951 (change p 10000 none)) = d1952 p
  rw [sub1, sub9022]
  rfl
theorem sub9024 (p : Pattern) : d3040 (change p 10000 none) = d3040 p := by
  change (if p 182 then d1952 (change p 10000 none) else d3039 (change p 10000 none)) = d3040 p
  rw [sub9023, sub9018]
  rfl
theorem sub9025 (p : Pattern) : d3041 (change p 10000 none) = d3041 p := by
  change (if p 163 then d3040 (change p 10000 none) else d3034 (change p 10000 none)) = d3041 p
  rw [sub9024, sub9013]
  rfl
theorem sub9026 (p : Pattern) : d1958 (change p 10000 none) = d1958 p := by
  change (if p 204 then d12 (change p 10000 none) else d1957 (change p 10000 none)) = d1958 p
  rw [sub1, sub8948]
  rfl
theorem sub9027 (p : Pattern) : d3042 (change p 10000 none) = d3042 p := by
  change (if p 182 then d1958 (change p 10000 none) else d3002 (change p 10000 none)) = d3042 p
  rw [sub9026, sub8949]
  rfl
theorem sub9028 (p : Pattern) : d1967 (change p 10000 none) = d1967 p := by
  change (if p 204 then d12 (change p 10000 none) else d1966 (change p 10000 none)) = d1967 p
  rw [sub1, sub8975]
  rfl
theorem sub9029 (p : Pattern) : d3043 (change p 10000 none) = d3043 p := by
  change (if p 182 then d1967 (change p 10000 none) else d3007 (change p 10000 none)) = d3043 p
  rw [sub9028, sub8976]
  rfl
theorem sub9030 (p : Pattern) : d3044 (change p 10000 none) = d3044 p := by
  change (if p 163 then d3043 (change p 10000 none) else d3042 (change p 10000 none)) = d3044 p
  rw [sub9029, sub9027]
  rfl
theorem sub9031 (p : Pattern) : d3045 (change p 10000 none) = d3045 p := by
  change (if p 162 then d3044 (change p 10000 none) else d3041 (change p 10000 none)) = d3045 p
  rw [sub9030, sub9025]
  rfl
theorem sub9032 (p : Pattern) : d3046 (change p 10000 none) = d3046 p := by
  change (if p 162 then d2999 (change p 10000 none) else d3044 (change p 10000 none)) = d3046 p
  rw [sub8940, sub9030]
  rfl
theorem sub9033 (p : Pattern) : d3047 (change p 10000 none) = d3047 p := by
  change (if p 161 then d3046 (change p 10000 none) else d3045 (change p 10000 none)) = d3047 p
  rw [sub9032, sub9031]
  rfl
theorem sub9034 (p : Pattern) : d3048 (change p 10000 none) = d3048 p := by
  change (if p 182 then d1899 (change p 10000 none) else d3023 (change p 10000 none)) = d3048 p
  rw [sub8958, sub8999]
  rfl
theorem sub9035 (p : Pattern) : d3049 (change p 10000 none) = d3049 p := by
  change (if p 204 then d1905 (change p 10000 none) else d120 (change p 10000 none)) = d3049 p
  rw [sub8965, sub119]
  rfl
theorem sub9036 (p : Pattern) : d3050 (change p 10000 none) = d3050 p := by
  change (if p 182 then d1906 (change p 10000 none) else d3049 (change p 10000 none)) = d3050 p
  rw [sub8966, sub9035]
  rfl
theorem sub9037 (p : Pattern) : d3051 (change p 10000 none) = d3051 p := by
  change (if p 163 then d3050 (change p 10000 none) else d3048 (change p 10000 none)) = d3051 p
  rw [sub9036, sub9034]
  rfl
theorem sub9038 (p : Pattern) : d3052 (change p 10000 none) = d3052 p := by
  change (if p 162 then d12 (change p 10000 none) else d3051 (change p 10000 none)) = d3052 p
  rw [sub1, sub9037]
  rfl
theorem sub9039 (p : Pattern) : d3053 (change p 10000 none) = d3053 p := by
  change (if p 161 then d12 (change p 10000 none) else d3052 (change p 10000 none)) = d3053 p
  rw [sub1, sub9038]
  rfl
theorem sub9040 (p : Pattern) : d3054 (change p 10000 none) = d3054 p := by
  change (if p 160 then d3053 (change p 10000 none) else d3047 (change p 10000 none)) = d3054 p
  rw [sub9039, sub9033]
  rfl
theorem sub9041 (p : Pattern) : d3055 (change p 10000 none) = d3055 p := by
  change (if p 163 then d3048 (change p 10000 none) else d3040 (change p 10000 none)) = d3055 p
  rw [sub9034, sub9024]
  rfl
theorem sub9042 (p : Pattern) : d3056 (change p 10000 none) = d3056 p := by
  change (if p 163 then d2928 (change p 10000 none) else d3043 (change p 10000 none)) = d3056 p
  rw [sub8836, sub9029]
  rfl
theorem sub9043 (p : Pattern) : d3057 (change p 10000 none) = d3057 p := by
  change (if p 162 then d3056 (change p 10000 none) else d3055 (change p 10000 none)) = d3057 p
  rw [sub9042, sub9041]
  rfl
theorem sub9044 (p : Pattern) : d3058 (change p 10000 none) = d3058 p := by
  change (if p 163 then d2931 (change p 10000 none) else d3043 (change p 10000 none)) = d3058 p
  rw [sub8839, sub9029]
  rfl
theorem sub9045 (p : Pattern) : d3059 (change p 10000 none) = d3059 p := by
  change (if p 162 then d12 (change p 10000 none) else d3058 (change p 10000 none)) = d3059 p
  rw [sub1, sub9044]
  rfl
theorem sub9046 (p : Pattern) : d3060 (change p 10000 none) = d3060 p := by
  change (if p 161 then d3059 (change p 10000 none) else d3057 (change p 10000 none)) = d3060 p
  rw [sub9045, sub9043]
  rfl
theorem sub9047 (p : Pattern) : d3061 (change p 10000 none) = d3061 p := by
  change (if p 163 then d12 (change p 10000 none) else d3050 (change p 10000 none)) = d3061 p
  rw [sub1, sub9036]
  rfl
theorem sub9048 (p : Pattern) : d3062 (change p 10000 none) = d3062 p := by
  change (if p 162 then d12 (change p 10000 none) else d3061 (change p 10000 none)) = d3062 p
  rw [sub1, sub9047]
  rfl
theorem sub9049 (p : Pattern) : d3063 (change p 10000 none) = d3063 p := by
  change (if p 161 then d12 (change p 10000 none) else d3062 (change p 10000 none)) = d3063 p
  rw [sub1, sub9048]
  rfl
theorem sub9050 (p : Pattern) : d3064 (change p 10000 none) = d3064 p := by
  change (if p 160 then d3063 (change p 10000 none) else d3060 (change p 10000 none)) = d3064 p
  rw [sub9049, sub9046]
  rfl
theorem sub9051 (p : Pattern) : d3065 (change p 10000 none) = d3065 p := by
  change (if p 141 then d3064 (change p 10000 none) else d3054 (change p 10000 none)) = d3065 p
  rw [sub9050, sub9040]
  rfl
theorem sub9052 (p : Pattern) : d3066 (change p 10000 none) = d3066 p := by
  change (if p 138 then d3065 (change p 10000 none) else d3032 (change p 10000 none)) = d3066 p
  rw [sub9051, sub9008]
  rfl
theorem sub9053 (p : Pattern) : d3067 (change p 10000 none) = d3067 p := by
  change (if p 162 then d12 (change p 10000 none) else d2999 (change p 10000 none)) = d3067 p
  rw [sub1, sub8940]
  rfl
theorem sub9054 (p : Pattern) : d3068 (change p 10000 none) = d3068 p := by
  change (if p 161 then d12 (change p 10000 none) else d3067 (change p 10000 none)) = d3068 p
  rw [sub1, sub9053]
  rfl
theorem sub9055 (p : Pattern) : d3069 (change p 10000 none) = d3069 p := by
  change (if p 160 then d12 (change p 10000 none) else d3068 (change p 10000 none)) = d3069 p
  rw [sub1, sub9054]
  rfl
theorem sub9056 (p : Pattern) : d3070 (change p 10000 none) = d3070 p := by
  change (if p 141 then d12 (change p 10000 none) else d3069 (change p 10000 none)) = d3070 p
  rw [sub1, sub9055]
  rfl
theorem sub9057 (p : Pattern) : d3071 (change p 10000 none) = d3071 p := by
  change (if p 138 then d3070 (change p 10000 none) else d3065 (change p 10000 none)) = d3071 p
  rw [sub9056, sub9051]
  rfl
theorem sub9058 (p : Pattern) : d3072 (change p 10000 none) = d3072 p := by
  change (if p 116 then d3071 (change p 10000 none) else d3066 (change p 10000 none)) = d3072 p
  rw [sub9057, sub9052]
  rfl
theorem sub9059 (p : Pattern) : d3073 (change p 10000 none) = d3073 p := by
  change (if p 138 then d12 (change p 10000 none) else d3065 (change p 10000 none)) = d3073 p
  rw [sub1, sub9051]
  rfl
theorem sub9060 (p : Pattern) : d3074 (change p 10000 none) = d3074 p := by
  change (if p 116 then d3073 (change p 10000 none) else d3066 (change p 10000 none)) = d3074 p
  rw [sub9059, sub9052]
  rfl
theorem sub9061 (p : Pattern) : d3075 (change p 10000 none) = d3075 p := by
  change (if p 115 then d3074 (change p 10000 none) else d3072 (change p 10000 none)) = d3075 p
  rw [sub9060, sub9058]
  rfl
theorem sub9062 (p : Pattern) : d3076 (change p 10000 none) = d3076 p := by
  change (if p 71 then d3075 (change p 10000 none) else d2992 (change p 10000 none)) = d3076 p
  rw [sub9061, sub8915]
  rfl
theorem sub9063 (p : Pattern) : d3077 (change p 10000 none) = d3077 p := by
  change (if p 49 then d3076 (change p 10000 none) else d2992 (change p 10000 none)) = d3077 p
  rw [sub9062, sub8915]
  rfl
theorem sub9064 (p : Pattern) : d3078 (change p 10000 none) = d3078 p := by
  change (if p 225 then d1792 (change p 10000 none) else d1795 (change p 10000 none)) = d3078 p
  rw [sub8804, sub8747]
  rfl
theorem sub9065 (p : Pattern) : d3079 (change p 10000 none) = d3079 p := by
  change (if p 224 then d3078 (change p 10000 none) else d1793 (change p 10000 none)) = d3079 p
  rw [sub9064, sub8805]
  rfl
theorem sub9066 (p : Pattern) : d3080 (change p 10000 none) = d3080 p := by
  change (if p 204 then d3079 (change p 10000 none) else d18 (change p 10000 none)) = d3080 p
  rw [sub9065, sub8]
  rfl
theorem sub9067 (p : Pattern) : d2013 (change p 10000 none) = d2013 p := by
  change (if p 204 then d12 (change p 10000 none) else d2012 (change p 10000 none)) = d2013 p
  rw [sub1, sub8749]
  rfl
theorem sub9068 (p : Pattern) : d3081 (change p 10000 none) = d3081 p := by
  change (if p 182 then d2013 (change p 10000 none) else d3080 (change p 10000 none)) = d3081 p
  rw [sub9067, sub9066]
  rfl
theorem sub9069 (p : Pattern) : d3082 (change p 10000 none) = d3082 p := by
  change (if p 163 then d3081 (change p 10000 none) else d2949 (change p 10000 none)) = d3082 p
  rw [sub9068, sub8860]
  rfl
theorem sub9070 (p : Pattern) : d3083 (change p 10000 none) = d3083 p := by
  change (if p 162 then d3082 (change p 10000 none) else d2949 (change p 10000 none)) = d3083 p
  rw [sub9069, sub8860]
  rfl
theorem sub9071 (p : Pattern) : d3084 (change p 10000 none) = d3084 p := by
  change (if p 162 then d2958 (change p 10000 none) else d3082 (change p 10000 none)) = d3084 p
  rw [sub8881, sub9069]
  rfl
theorem sub9072 (p : Pattern) : d3085 (change p 10000 none) = d3085 p := by
  change (if p 161 then d3084 (change p 10000 none) else d3083 (change p 10000 none)) = d3085 p
  rw [sub9071, sub9070]
  rfl
theorem sub9073 (p : Pattern) : d3086 (change p 10000 none) = d3086 p := by
  change (if p 182 then d1725 (change p 10000 none) else d2935 (change p 10000 none)) = d3086 p
  rw [sub8795, sub8843]
  rfl
theorem sub9074 (p : Pattern) : d3087 (change p 10000 none) = d3087 p := by
  change (if p 163 then d3086 (change p 10000 none) else d2961 (change p 10000 none)) = d3087 p
  rw [sub9073, sub8884]
  rfl
theorem sub9075 (p : Pattern) : d3088 (change p 10000 none) = d3088 p := by
  change (if p 182 then d1730 (change p 10000 none) else d2935 (change p 10000 none)) = d3088 p
  rw [sub8801, sub8843]
  rfl
theorem sub9076 (p : Pattern) : d3089 (change p 10000 none) = d3089 p := by
  change (if p 182 then d12 (change p 10000 none) else d2962 (change p 10000 none)) = d3089 p
  rw [sub1, sub8885]
  rfl
theorem sub9077 (p : Pattern) : d3090 (change p 10000 none) = d3090 p := by
  change (if p 163 then d3089 (change p 10000 none) else d3088 (change p 10000 none)) = d3090 p
  rw [sub9076, sub9075]
  rfl
theorem sub9078 (p : Pattern) : d3091 (change p 10000 none) = d3091 p := by
  change (if p 162 then d3090 (change p 10000 none) else d3087 (change p 10000 none)) = d3091 p
  rw [sub9077, sub9074]
  rfl
theorem sub9079 (p : Pattern) : d3092 (change p 10000 none) = d3092 p := by
  change (if p 163 then d3089 (change p 10000 none) else d2936 (change p 10000 none)) = d3092 p
  rw [sub9076, sub8844]
  rfl
theorem sub9080 (p : Pattern) : d3093 (change p 10000 none) = d3093 p := by
  change (if p 162 then d2943 (change p 10000 none) else d3092 (change p 10000 none)) = d3093 p
  rw [sub8851, sub9079]
  rfl
theorem sub9081 (p : Pattern) : d3094 (change p 10000 none) = d3094 p := by
  change (if p 161 then d3093 (change p 10000 none) else d3091 (change p 10000 none)) = d3094 p
  rw [sub9080, sub9078]
  rfl
theorem sub9082 (p : Pattern) : d3095 (change p 10000 none) = d3095 p := by
  change (if p 160 then d3094 (change p 10000 none) else d3085 (change p 10000 none)) = d3095 p
  rw [sub9081, sub9072]
  rfl
theorem sub9083 (p : Pattern) : d3096 (change p 10000 none) = d3096 p := by
  change (if p 225 then d1711 (change p 10000 none) else d1714 (change p 10000 none)) = d3096 p
  rw [sub8780, sub8783]
  rfl
theorem sub9084 (p : Pattern) : d3097 (change p 10000 none) = d3097 p := by
  change (if p 224 then d3096 (change p 10000 none) else d1712 (change p 10000 none)) = d3097 p
  rw [sub9083, sub8781]
  rfl
theorem sub9085 (p : Pattern) : d3098 (change p 10000 none) = d3098 p := by
  change (if p 204 then d3097 (change p 10000 none) else d31 (change p 10000 none)) = d3098 p
  rw [sub9084, sub23]
  rfl
theorem sub9086 (p : Pattern) : d2031 (change p 10000 none) = d2031 p := by
  change (if p 204 then d12 (change p 10000 none) else d2030 (change p 10000 none)) = d2031 p
  rw [sub1, sub8821]
  rfl
theorem sub9087 (p : Pattern) : d3099 (change p 10000 none) = d3099 p := by
  change (if p 182 then d2031 (change p 10000 none) else d3098 (change p 10000 none)) = d3099 p
  rw [sub9086, sub9085]
  rfl
theorem sub9088 (p : Pattern) : d3100 (change p 10000 none) = d3100 p := by
  change (if p 163 then d3099 (change p 10000 none) else d2949 (change p 10000 none)) = d3100 p
  rw [sub9087, sub8860]
  rfl
theorem sub9089 (p : Pattern) : d3101 (change p 10000 none) = d3101 p := by
  change (if p 163 then d2957 (change p 10000 none) else d3081 (change p 10000 none)) = d3101 p
  rw [sub8880, sub9068]
  rfl
theorem sub9090 (p : Pattern) : d3102 (change p 10000 none) = d3102 p := by
  change (if p 162 then d3101 (change p 10000 none) else d3100 (change p 10000 none)) = d3102 p
  rw [sub9089, sub9088]
  rfl
theorem sub9091 (p : Pattern) : d3103 (change p 10000 none) = d3103 p := by
  change (if p 163 then d2928 (change p 10000 none) else d3081 (change p 10000 none)) = d3103 p
  rw [sub8836, sub9068]
  rfl
theorem sub9092 (p : Pattern) : d3104 (change p 10000 none) = d3104 p := by
  change (if p 162 then d2932 (change p 10000 none) else d3103 (change p 10000 none)) = d3104 p
  rw [sub8840, sub9091]
  rfl
theorem sub9093 (p : Pattern) : d3105 (change p 10000 none) = d3105 p := by
  change (if p 161 then d3104 (change p 10000 none) else d3102 (change p 10000 none)) = d3105 p
  rw [sub9092, sub9090]
  rfl
theorem sub9094 (p : Pattern) : d3106 (change p 10000 none) = d3106 p := by
  change (if p 163 then d2912 (change p 10000 none) else d3086 (change p 10000 none)) = d3106 p
  rw [sub8810, sub9073]
  rfl
theorem sub9095 (p : Pattern) : d3107 (change p 10000 none) = d3107 p := by
  change (if p 163 then d2942 (change p 10000 none) else d3089 (change p 10000 none)) = d3107 p
  rw [sub8850, sub9076]
  rfl
theorem sub9096 (p : Pattern) : d3108 (change p 10000 none) = d3108 p := by
  change (if p 162 then d3107 (change p 10000 none) else d3106 (change p 10000 none)) = d3108 p
  rw [sub9095, sub9094]
  rfl
theorem sub9097 (p : Pattern) : d3109 (change p 10000 none) = d3109 p := by
  change (if p 163 then d12 (change p 10000 none) else d3089 (change p 10000 none)) = d3109 p
  rw [sub1, sub9076]
  rfl
theorem sub9098 (p : Pattern) : d3110 (change p 10000 none) = d3110 p := by
  change (if p 162 then d12 (change p 10000 none) else d3109 (change p 10000 none)) = d3110 p
  rw [sub1, sub9097]
  rfl
theorem sub9099 (p : Pattern) : d3111 (change p 10000 none) = d3111 p := by
  change (if p 161 then d3110 (change p 10000 none) else d3108 (change p 10000 none)) = d3111 p
  rw [sub9098, sub9096]
  rfl
theorem sub9100 (p : Pattern) : d3112 (change p 10000 none) = d3112 p := by
  change (if p 160 then d3111 (change p 10000 none) else d3105 (change p 10000 none)) = d3112 p
  rw [sub9099, sub9093]
  rfl
theorem sub9101 (p : Pattern) : d3113 (change p 10000 none) = d3113 p := by
  change (if p 141 then d3112 (change p 10000 none) else d3095 (change p 10000 none)) = d3113 p
  rw [sub9100, sub9082]
  rfl
theorem sub9102 (p : Pattern) : d3114 (change p 10000 none) = d3114 p := by
  change (if p 204 then d1781 (change p 10000 none) else d14 (change p 10000 none)) = d3114 p
  rw [sub8869, sub3]
  rfl
theorem sub9103 (p : Pattern) : d2049 (change p 10000 none) = d2049 p := by
  change (if p 204 then d12 (change p 10000 none) else d2048 (change p 10000 none)) = d2049 p
  rw [sub1, sub8857]
  rfl
theorem sub9104 (p : Pattern) : d3115 (change p 10000 none) = d3115 p := by
  change (if p 182 then d2049 (change p 10000 none) else d3114 (change p 10000 none)) = d3115 p
  rw [sub9103, sub9102]
  rfl
theorem sub9105 (p : Pattern) : d2055 (change p 10000 none) = d2055 p := by
  change (if p 204 then d12 (change p 10000 none) else d2054 (change p 10000 none)) = d2055 p
  rw [sub1, sub8864]
  rfl
theorem sub9106 (p : Pattern) : d3116 (change p 10000 none) = d3116 p := by
  change (if p 182 then d2055 (change p 10000 none) else d2906 (change p 10000 none)) = d3116 p
  rw [sub9105, sub8778]
  rfl
theorem sub9107 (p : Pattern) : d3117 (change p 10000 none) = d3117 p := by
  change (if p 163 then d3116 (change p 10000 none) else d3115 (change p 10000 none)) = d3117 p
  rw [sub9106, sub9104]
  rfl
theorem sub9108 (p : Pattern) : d3118 (change p 10000 none) = d3118 p := by
  change (if p 162 then d2964 (change p 10000 none) else d3117 (change p 10000 none)) = d3118 p
  rw [sub8887, sub9107]
  rfl
theorem sub9109 (p : Pattern) : d3119 (change p 10000 none) = d3119 p := by
  change (if p 161 then d2965 (change p 10000 none) else d3118 (change p 10000 none)) = d3119 p
  rw [sub8888, sub9108]
  rfl
theorem sub9110 (p : Pattern) : d315 (change p 10000 none) = d315 p := by
  change (if p 246 then d12 (change p 10000 none) else d190 (change p 10000 none)) = d315 p
  rw [sub1, sub190]
  rfl
theorem sub9111 (p : Pattern) : d2060 (change p 10000 none) = d2060 p := by
  change (if p 225 then d315 (change p 10000 none) else d191 (change p 10000 none)) = d2060 p
  rw [sub9110, sub191]
  rfl
theorem sub9112 (p : Pattern) : d2061 (change p 10000 none) = d2061 p := by
  change (if p 224 then d315 (change p 10000 none) else d2060 (change p 10000 none)) = d2061 p
  rw [sub9110, sub9111]
  rfl
theorem sub9113 (p : Pattern) : d3120 (change p 10000 none) = d3120 p := by
  change (if p 204 then d2061 (change p 10000 none) else d191 (change p 10000 none)) = d3120 p
  rw [sub9112, sub191]
  rfl
theorem sub9114 (p : Pattern) : d2062 (change p 10000 none) = d2062 p := by
  change (if p 204 then d12 (change p 10000 none) else d2061 (change p 10000 none)) = d2062 p
  rw [sub1, sub9112]
  rfl
theorem sub9115 (p : Pattern) : d3121 (change p 10000 none) = d3121 p := by
  change (if p 182 then d2062 (change p 10000 none) else d3120 (change p 10000 none)) = d3121 p
  rw [sub9114, sub9113]
  rfl
theorem sub9116 (p : Pattern) : d3122 (change p 10000 none) = d3122 p := by
  change (if p 163 then d3121 (change p 10000 none) else d2954 (change p 10000 none)) = d3122 p
  rw [sub9115, sub8876]
  rfl
theorem sub9117 (p : Pattern) : d3123 (change p 10000 none) = d3123 p := by
  change (if p 162 then d12 (change p 10000 none) else d3122 (change p 10000 none)) = d3123 p
  rw [sub1, sub9116]
  rfl
theorem sub9118 (p : Pattern) : d3124 (change p 10000 none) = d3124 p := by
  change (if p 161 then d12 (change p 10000 none) else d3123 (change p 10000 none)) = d3124 p
  rw [sub1, sub9117]
  rfl
theorem sub9119 (p : Pattern) : d3125 (change p 10000 none) = d3125 p := by
  change (if p 160 then d3124 (change p 10000 none) else d3119 (change p 10000 none)) = d3125 p
  rw [sub9118, sub9109]
  rfl
end NetHack.Sokoban22Refined85
