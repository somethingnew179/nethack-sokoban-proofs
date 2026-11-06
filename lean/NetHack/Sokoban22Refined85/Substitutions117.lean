/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions116
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub14040 (p : Pattern) : d3097 (change p 10000 (some 247)) = d7940 p := by
  change (if p 224 then d3096 (change p 10000 (some 247)) else d1712 (change p 10000 (some 247))) = d7940 p
  rw [sub14039, sub13719]
  rfl
theorem sub14041 (p : Pattern) : d3098 (change p 10000 (some 247)) = d7941 p := by
  change (if p 204 then d3097 (change p 10000 (some 247)) else d31 (change p 10000 (some 247))) = d7941 p
  rw [sub14040, sub13716]
  rfl
theorem sub14042 (p : Pattern) : d2031 (change p 10000 (some 247)) = d7942 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d2030 (change p 10000 (some 247))) = d7942 p
  rw [sub13654, sub13763]
  rfl
theorem sub14043 (p : Pattern) : d3099 (change p 10000 (some 247)) = d7943 p := by
  change (if p 182 then d2031 (change p 10000 (some 247)) else d3098 (change p 10000 (some 247))) = d7943 p
  rw [sub14042, sub14041]
  rfl
theorem sub14044 (p : Pattern) : d3100 (change p 10000 (some 247)) = d7944 p := by
  change (if p 163 then d3099 (change p 10000 (some 247)) else d2949 (change p 10000 (some 247))) = d7944 p
  rw [sub14043, sub13804]
  rfl
theorem sub14045 (p : Pattern) : d3101 (change p 10000 (some 247)) = d7945 p := by
  change (if p 163 then d2957 (change p 10000 (some 247)) else d3081 (change p 10000 (some 247))) = d7945 p
  rw [sub13824, sub14024]
  rfl
theorem sub14046 (p : Pattern) : d3102 (change p 10000 (some 247)) = d7946 p := by
  change (if p 162 then d3101 (change p 10000 (some 247)) else d3100 (change p 10000 (some 247))) = d7946 p
  rw [sub14045, sub14044]
  rfl
theorem sub14047 (p : Pattern) : d3103 (change p 10000 (some 247)) = d7947 p := by
  change (if p 163 then d2928 (change p 10000 (some 247)) else d3081 (change p 10000 (some 247))) = d7947 p
  rw [sub13780, sub14024]
  rfl
theorem sub14048 (p : Pattern) : d3104 (change p 10000 (some 247)) = d7948 p := by
  change (if p 162 then d2932 (change p 10000 (some 247)) else d3103 (change p 10000 (some 247))) = d7948 p
  rw [sub13784, sub14047]
  rfl
theorem sub14049 (p : Pattern) : d3105 (change p 10000 (some 247)) = d7949 p := by
  change (if p 161 then d3104 (change p 10000 (some 247)) else d3102 (change p 10000 (some 247))) = d7949 p
  rw [sub14048, sub14046]
  rfl
theorem sub14050 (p : Pattern) : d3106 (change p 10000 (some 247)) = d7950 p := by
  change (if p 163 then d2912 (change p 10000 (some 247)) else d3086 (change p 10000 (some 247))) = d7950 p
  rw [sub13752, sub14029]
  rfl
theorem sub14051 (p : Pattern) : d3107 (change p 10000 (some 247)) = d7951 p := by
  change (if p 163 then d2942 (change p 10000 (some 247)) else d3089 (change p 10000 (some 247))) = d7951 p
  rw [sub13794, sub14032]
  rfl
theorem sub14052 (p : Pattern) : d3108 (change p 10000 (some 247)) = d7952 p := by
  change (if p 162 then d3107 (change p 10000 (some 247)) else d3106 (change p 10000 (some 247))) = d7952 p
  rw [sub14051, sub14050]
  rfl
theorem sub14053 (p : Pattern) : d3109 (change p 10000 (some 247)) = d7953 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d3089 (change p 10000 (some 247))) = d7953 p
  rw [sub13654, sub14032]
  rfl
theorem sub14054 (p : Pattern) : d3110 (change p 10000 (some 247)) = d7954 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d3109 (change p 10000 (some 247))) = d7954 p
  rw [sub13654, sub14053]
  rfl
theorem sub14055 (p : Pattern) : d3111 (change p 10000 (some 247)) = d7955 p := by
  change (if p 161 then d3110 (change p 10000 (some 247)) else d3108 (change p 10000 (some 247))) = d7955 p
  rw [sub14054, sub14052]
  rfl
theorem sub14056 (p : Pattern) : d3112 (change p 10000 (some 247)) = d7956 p := by
  change (if p 160 then d3111 (change p 10000 (some 247)) else d3105 (change p 10000 (some 247))) = d7956 p
  rw [sub14055, sub14049]
  rfl
theorem sub14057 (p : Pattern) : d3113 (change p 10000 (some 247)) = d7957 p := by
  change (if p 141 then d3112 (change p 10000 (some 247)) else d3095 (change p 10000 (some 247))) = d7957 p
  rw [sub14056, sub14038]
  rfl
theorem sub14058 (p : Pattern) : d3114 (change p 10000 (some 247)) = d7958 p := by
  change (if p 204 then d1781 (change p 10000 (some 247)) else d14 (change p 10000 (some 247))) = d7958 p
  rw [sub13813, sub13656]
  rfl
theorem sub14059 (p : Pattern) : d2049 (change p 10000 (some 247)) = d7959 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d2048 (change p 10000 (some 247))) = d7959 p
  rw [sub13654, sub13801]
  rfl
theorem sub14060 (p : Pattern) : d3115 (change p 10000 (some 247)) = d7960 p := by
  change (if p 182 then d2049 (change p 10000 (some 247)) else d3114 (change p 10000 (some 247))) = d7960 p
  rw [sub14059, sub14058]
  rfl
theorem sub14061 (p : Pattern) : d2055 (change p 10000 (some 247)) = d7961 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d2054 (change p 10000 (some 247))) = d7961 p
  rw [sub13654, sub13808]
  rfl
theorem sub14062 (p : Pattern) : d3116 (change p 10000 (some 247)) = d7962 p := by
  change (if p 182 then d2055 (change p 10000 (some 247)) else d2906 (change p 10000 (some 247))) = d7962 p
  rw [sub14061, sub13715]
  rfl
theorem sub14063 (p : Pattern) : d3117 (change p 10000 (some 247)) = d7963 p := by
  change (if p 163 then d3116 (change p 10000 (some 247)) else d3115 (change p 10000 (some 247))) = d7963 p
  rw [sub14062, sub14060]
  rfl
theorem sub14064 (p : Pattern) : d3118 (change p 10000 (some 247)) = d7964 p := by
  change (if p 162 then d2964 (change p 10000 (some 247)) else d3117 (change p 10000 (some 247))) = d7964 p
  rw [sub13831, sub14063]
  rfl
theorem sub14065 (p : Pattern) : d3119 (change p 10000 (some 247)) = d7965 p := by
  change (if p 161 then d2965 (change p 10000 (some 247)) else d3118 (change p 10000 (some 247))) = d7965 p
  rw [sub13832, sub14064]
  rfl
theorem sub14066 (p : Pattern) : d191 (change p 10000 (some 247)) = d3461 p := by
  change (if p 246 then d190 (change p 10000 (some 247)) else d8 (change p 10000 (some 247))) = d3461 p
  rw [sub13675, sub13673]
  rfl
theorem sub14067 (p : Pattern) : d315 (change p 10000 (some 247)) = d12 p := by
  change (if p 246 then d12 (change p 10000 (some 247)) else d190 (change p 10000 (some 247))) = d12 p
  rw [sub13654, sub13675]
  simp only [ite_self]
theorem sub14068 (p : Pattern) : d2060 (change p 10000 (some 247)) = d7707 p := by
  change (if p 225 then d315 (change p 10000 (some 247)) else d191 (change p 10000 (some 247))) = d7707 p
  rw [sub14067, sub14066]
  rfl
theorem sub14069 (p : Pattern) : d2061 (change p 10000 (some 247)) = d7966 p := by
  change (if p 224 then d315 (change p 10000 (some 247)) else d2060 (change p 10000 (some 247))) = d7966 p
  rw [sub14067, sub14068]
  rfl
theorem sub14070 (p : Pattern) : d3120 (change p 10000 (some 247)) = d7967 p := by
  change (if p 204 then d2061 (change p 10000 (some 247)) else d191 (change p 10000 (some 247))) = d7967 p
  rw [sub14069, sub14066]
  rfl
theorem sub14071 (p : Pattern) : d2062 (change p 10000 (some 247)) = d7968 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d2061 (change p 10000 (some 247))) = d7968 p
  rw [sub13654, sub14069]
  rfl
theorem sub14072 (p : Pattern) : d3121 (change p 10000 (some 247)) = d7969 p := by
  change (if p 182 then d2062 (change p 10000 (some 247)) else d3120 (change p 10000 (some 247))) = d7969 p
  rw [sub14071, sub14070]
  rfl
theorem sub14073 (p : Pattern) : d3122 (change p 10000 (some 247)) = d7970 p := by
  change (if p 163 then d3121 (change p 10000 (some 247)) else d2954 (change p 10000 (some 247))) = d7970 p
  rw [sub14072, sub13820]
  rfl
theorem sub14074 (p : Pattern) : d3123 (change p 10000 (some 247)) = d7971 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d3122 (change p 10000 (some 247))) = d7971 p
  rw [sub13654, sub14073]
  rfl
theorem sub14075 (p : Pattern) : d3124 (change p 10000 (some 247)) = d7972 p := by
  change (if p 161 then d12 (change p 10000 (some 247)) else d3123 (change p 10000 (some 247))) = d7972 p
  rw [sub13654, sub14074]
  rfl
theorem sub14076 (p : Pattern) : d3125 (change p 10000 (some 247)) = d7973 p := by
  change (if p 160 then d3124 (change p 10000 (some 247)) else d3119 (change p 10000 (some 247))) = d7973 p
  rw [sub14075, sub14065]
  rfl
theorem sub14077 (p : Pattern) : d2068 (change p 10000 (some 247)) = d10 p := by
  change d10 (change p 10000 (some 247)) = d10 p
  exact sub13730 p
theorem sub14078 (p : Pattern) : d2069 (change p 10000 (some 247)) = d3279 p := by
  change (if p 246 then d57 (change p 10000 (some 247)) else d2068 (change p 10000 (some 247))) = d3279 p
  rw [sub13732, sub14077]
  rfl
theorem sub14079 (p : Pattern) : d2070 (change p 10000 (some 247)) = d7974 p := by
  change (if p 225 then d2069 (change p 10000 (some 247)) else d1714 (change p 10000 (some 247))) = d7974 p
  rw [sub14078, sub13721]
  rfl
theorem sub14080 (p : Pattern) : d2071 (change p 10000 (some 247)) = d7975 p := by
  change (if p 224 then d2070 (change p 10000 (some 247)) else d1712 (change p 10000 (some 247))) = d7975 p
  rw [sub14079, sub13719]
  rfl
theorem sub14081 (p : Pattern) : d2072 (change p 10000 (some 247)) = d7976 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d2071 (change p 10000 (some 247))) = d7976 p
  rw [sub13654, sub14080]
  rfl
theorem sub14082 (p : Pattern) : d3126 (change p 10000 (some 247)) = d7977 p := by
  change (if p 182 then d2072 (change p 10000 (some 247)) else d2935 (change p 10000 (some 247))) = d7977 p
  rw [sub14081, sub13787]
  rfl
theorem sub14083 (p : Pattern) : d3127 (change p 10000 (some 247)) = d7978 p := by
  change (if p 163 then d2961 (change p 10000 (some 247)) else d3126 (change p 10000 (some 247))) = d7978 p
  rw [sub13828, sub14082]
  rfl
theorem sub14084 (p : Pattern) : d3128 (change p 10000 (some 247)) = d7979 p := by
  change (if p 163 then d2931 (change p 10000 (some 247)) else d2954 (change p 10000 (some 247))) = d7979 p
  rw [sub13783, sub13820]
  rfl
theorem sub14085 (p : Pattern) : d3129 (change p 10000 (some 247)) = d7980 p := by
  change (if p 162 then d3128 (change p 10000 (some 247)) else d3127 (change p 10000 (some 247))) = d7980 p
  rw [sub14084, sub14083]
  rfl
theorem sub14086 (p : Pattern) : d3130 (change p 10000 (some 247)) = d7981 p := by
  change (if p 161 then d2975 (change p 10000 (some 247)) else d3129 (change p 10000 (some 247))) = d7981 p
  rw [sub13842, sub14085]
  rfl
theorem sub14087 (p : Pattern) : d3131 (change p 10000 (some 247)) = d7982 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d3121 (change p 10000 (some 247))) = d7982 p
  rw [sub13654, sub14072]
  rfl
theorem sub14088 (p : Pattern) : d3132 (change p 10000 (some 247)) = d7983 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d3131 (change p 10000 (some 247))) = d7983 p
  rw [sub13654, sub14087]
  rfl
theorem sub14089 (p : Pattern) : d3133 (change p 10000 (some 247)) = d7984 p := by
  change (if p 161 then d12 (change p 10000 (some 247)) else d3132 (change p 10000 (some 247))) = d7984 p
  rw [sub13654, sub14088]
  rfl
theorem sub14090 (p : Pattern) : d3134 (change p 10000 (some 247)) = d7985 p := by
  change (if p 160 then d3133 (change p 10000 (some 247)) else d3130 (change p 10000 (some 247))) = d7985 p
  rw [sub14089, sub14086]
  rfl
theorem sub14091 (p : Pattern) : d3135 (change p 10000 (some 247)) = d7986 p := by
  change (if p 141 then d3134 (change p 10000 (some 247)) else d3125 (change p 10000 (some 247))) = d7986 p
  rw [sub14090, sub14076]
  rfl
theorem sub14092 (p : Pattern) : d3136 (change p 10000 (some 247)) = d7987 p := by
  change (if p 138 then d3135 (change p 10000 (some 247)) else d3113 (change p 10000 (some 247))) = d7987 p
  rw [sub14091, sub14057]
  rfl
theorem sub14093 (p : Pattern) : d3137 (change p 10000 (some 247)) = d7988 p := by
  change (if p 138 then d12 (change p 10000 (some 247)) else d3135 (change p 10000 (some 247))) = d7988 p
  rw [sub13654, sub14091]
  rfl
theorem sub14094 (p : Pattern) : d3138 (change p 10000 (some 247)) = d7989 p := by
  change (if p 116 then d3137 (change p 10000 (some 247)) else d3136 (change p 10000 (some 247))) = d7989 p
  rw [sub14093, sub14092]
  rfl
theorem sub14095 (p : Pattern) : d3139 (change p 10000 (some 247)) = d7990 p := by
  change (if p 115 then d3138 (change p 10000 (some 247)) else d2989 (change p 10000 (some 247))) = d7990 p
  rw [sub14094, sub13856]
  rfl
theorem sub14096 (p : Pattern) : d3140 (change p 10000 (some 247)) = d7991 p := by
  change (if p 71 then d3139 (change p 10000 (some 247)) else d2992 (change p 10000 (some 247))) = d7991 p
  rw [sub14095, sub13859]
  rfl
theorem sub14097 (p : Pattern) : d3141 (change p 10000 (some 247)) = d7992 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d2996 (change p 10000 (some 247))) = d7992 p
  rw [sub13654, sub13891]
  rfl
theorem sub14098 (p : Pattern) : d3142 (change p 10000 (some 247)) = d7993 p := by
  change (if p 162 then d3141 (change p 10000 (some 247)) else d3017 (change p 10000 (some 247))) = d7993 p
  rw [sub14097, sub13949]
  rfl
theorem sub14099 (p : Pattern) : d3143 (change p 10000 (some 247)) = d7994 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d3141 (change p 10000 (some 247))) = d7994 p
  rw [sub13654, sub14097]
  rfl
theorem sub14100 (p : Pattern) : d3144 (change p 10000 (some 247)) = d7995 p := by
  change (if p 161 then d3143 (change p 10000 (some 247)) else d3142 (change p 10000 (some 247))) = d7995 p
  rw [sub14099, sub14098]
  rfl
theorem sub14101 (p : Pattern) : d3145 (change p 10000 (some 247)) = d7996 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d3008 (change p 10000 (some 247))) = d7996 p
  rw [sub13654, sub13933]
  rfl
theorem sub14102 (p : Pattern) : d3146 (change p 10000 (some 247)) = d7997 p := by
  change (if p 162 then d3145 (change p 10000 (some 247)) else d3025 (change p 10000 (some 247))) = d7997 p
  rw [sub14101, sub13957]
  rfl
theorem sub14103 (p : Pattern) : d3147 (change p 10000 (some 247)) = d7998 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d3145 (change p 10000 (some 247))) = d7998 p
  rw [sub13654, sub14101]
  rfl
theorem sub14104 (p : Pattern) : d3148 (change p 10000 (some 247)) = d7999 p := by
  change (if p 161 then d3147 (change p 10000 (some 247)) else d3146 (change p 10000 (some 247))) = d7999 p
  rw [sub14103, sub14102]
  rfl
theorem sub14105 (p : Pattern) : d3149 (change p 10000 (some 247)) = d8000 p := by
  change (if p 160 then d3148 (change p 10000 (some 247)) else d3144 (change p 10000 (some 247))) = d8000 p
  rw [sub14104, sub14100]
  rfl
theorem sub14106 (p : Pattern) : d3150 (change p 10000 (some 247)) = d8001 p := by
  change (if p 141 then d3149 (change p 10000 (some 247)) else d3014 (change p 10000 (some 247))) = d8001 p
  rw [sub14105, sub13939]
  rfl
theorem sub14107 (p : Pattern) : d3151 (change p 10000 (some 247)) = d8002 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d3043 (change p 10000 (some 247))) = d8002 p
  rw [sub13654, sub13985]
  rfl
theorem sub14108 (p : Pattern) : d3152 (change p 10000 (some 247)) = d8003 p := by
  change (if p 162 then d3151 (change p 10000 (some 247)) else d3055 (change p 10000 (some 247))) = d8003 p
  rw [sub14107, sub13997]
  rfl
theorem sub14109 (p : Pattern) : d3153 (change p 10000 (some 247)) = d8004 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d3151 (change p 10000 (some 247))) = d8004 p
  rw [sub13654, sub14107]
  rfl
theorem sub14110 (p : Pattern) : d3154 (change p 10000 (some 247)) = d8005 p := by
  change (if p 161 then d3153 (change p 10000 (some 247)) else d3152 (change p 10000 (some 247))) = d8005 p
  rw [sub14109, sub14108]
  rfl
theorem sub14111 (p : Pattern) : d3155 (change p 10000 (some 247)) = d8006 p := by
  change (if p 160 then d3063 (change p 10000 (some 247)) else d3154 (change p 10000 (some 247))) = d8006 p
  rw [sub14005, sub14110]
  rfl
theorem sub14112 (p : Pattern) : d3156 (change p 10000 (some 247)) = d8007 p := by
  change (if p 141 then d3155 (change p 10000 (some 247)) else d3054 (change p 10000 (some 247))) = d8007 p
  rw [sub14111, sub13996]
  rfl
theorem sub14113 (p : Pattern) : d3157 (change p 10000 (some 247)) = d8008 p := by
  change (if p 138 then d3156 (change p 10000 (some 247)) else d3150 (change p 10000 (some 247))) = d8008 p
  rw [sub14112, sub14106]
  rfl
theorem sub14114 (p : Pattern) : d3158 (change p 10000 (some 247)) = d8009 p := by
  change (if p 138 then d3070 (change p 10000 (some 247)) else d3156 (change p 10000 (some 247))) = d8009 p
  rw [sub14012, sub14112]
  rfl
theorem sub14115 (p : Pattern) : d3159 (change p 10000 (some 247)) = d8010 p := by
  change (if p 116 then d3158 (change p 10000 (some 247)) else d3157 (change p 10000 (some 247))) = d8010 p
  rw [sub14114, sub14113]
  rfl
theorem sub14116 (p : Pattern) : d3160 (change p 10000 (some 247)) = d8011 p := by
  change (if p 204 then d1951 (change p 10000 (some 247)) else d103 (change p 10000 (some 247))) = d8011 p
  rw [sub13978, sub13862]
  rfl
theorem sub14117 (p : Pattern) : d2109 (change p 10000 (some 247)) = d8012 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d2108 (change p 10000 (some 247))) = d8012 p
  rw [sub13654, sub13966]
  rfl
theorem sub14118 (p : Pattern) : d3161 (change p 10000 (some 247)) = d8013 p := by
  change (if p 182 then d2109 (change p 10000 (some 247)) else d3160 (change p 10000 (some 247))) = d8013 p
  rw [sub14117, sub14116]
  rfl
theorem sub14119 (p : Pattern) : d3162 (change p 10000 (some 247)) = d8014 p := by
  change (if p 163 then d3043 (change p 10000 (some 247)) else d3161 (change p 10000 (some 247))) = d8014 p
  rw [sub13985, sub14118]
  rfl
theorem sub14120 (p : Pattern) : d3163 (change p 10000 (some 247)) = d8015 p := by
  change (if p 162 then d3162 (change p 10000 (some 247)) else d3034 (change p 10000 (some 247))) = d8015 p
  rw [sub14119, sub13969]
  rfl
theorem sub14121 (p : Pattern) : d3164 (change p 10000 (some 247)) = d8016 p := by
  change (if p 163 then d3043 (change p 10000 (some 247)) else d3040 (change p 10000 (some 247))) = d8016 p
  rw [sub13985, sub13980]
  rfl
theorem sub14122 (p : Pattern) : d3165 (change p 10000 (some 247)) = d8017 p := by
  change (if p 162 then d2999 (change p 10000 (some 247)) else d3164 (change p 10000 (some 247))) = d8017 p
  rw [sub13894, sub14121]
  rfl
theorem sub14123 (p : Pattern) : d3166 (change p 10000 (some 247)) = d8018 p := by
  change (if p 161 then d3165 (change p 10000 (some 247)) else d3163 (change p 10000 (some 247))) = d8018 p
  rw [sub14122, sub14120]
  rfl
theorem sub14124 (p : Pattern) : d3167 (change p 10000 (some 247)) = d8019 p := by
  change (if p 182 then d1906 (change p 10000 (some 247)) else d3023 (change p 10000 (some 247))) = d8019 p
  rw [sub13922, sub13955]
  rfl
theorem sub14125 (p : Pattern) : d3168 (change p 10000 (some 247)) = d8020 p := by
  change (if p 163 then d3167 (change p 10000 (some 247)) else d3048 (change p 10000 (some 247))) = d8020 p
  rw [sub14124, sub13990]
  rfl
theorem sub14126 (p : Pattern) : d3169 (change p 10000 (some 247)) = d8021 p := by
  change (if p 162 then d3145 (change p 10000 (some 247)) else d3168 (change p 10000 (some 247))) = d8021 p
  rw [sub14101, sub14125]
  rfl
theorem sub14127 (p : Pattern) : d3170 (change p 10000 (some 247)) = d8022 p := by
  change (if p 182 then d12 (change p 10000 (some 247)) else d3049 (change p 10000 (some 247))) = d8022 p
  rw [sub13654, sub13991]
  rfl
theorem sub14128 (p : Pattern) : d3171 (change p 10000 (some 247)) = d8023 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d3170 (change p 10000 (some 247))) = d8023 p
  rw [sub13654, sub14127]
  rfl
theorem sub14129 (p : Pattern) : d3172 (change p 10000 (some 247)) = d8024 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d3171 (change p 10000 (some 247))) = d8024 p
  rw [sub13654, sub14128]
  rfl
theorem sub14130 (p : Pattern) : d3173 (change p 10000 (some 247)) = d8025 p := by
  change (if p 161 then d3172 (change p 10000 (some 247)) else d3169 (change p 10000 (some 247))) = d8025 p
  rw [sub14129, sub14126]
  rfl
theorem sub14131 (p : Pattern) : d3174 (change p 10000 (some 247)) = d8026 p := by
  change (if p 160 then d3173 (change p 10000 (some 247)) else d3166 (change p 10000 (some 247))) = d8026 p
  rw [sub14130, sub14123]
  rfl
theorem sub14132 (p : Pattern) : d3175 (change p 10000 (some 247)) = d8027 p := by
  change (if p 225 then d1892 (change p 10000 (some 247)) else d1895 (change p 10000 (some 247))) = d8027 p
  rw [sub13906, sub13909]
  rfl
theorem sub14133 (p : Pattern) : d3176 (change p 10000 (some 247)) = d8028 p := by
  change (if p 224 then d3175 (change p 10000 (some 247)) else d1893 (change p 10000 (some 247))) = d8028 p
  rw [sub14132, sub13907]
  rfl
theorem sub14134 (p : Pattern) : d3177 (change p 10000 (some 247)) = d8029 p := by
  change (if p 204 then d3176 (change p 10000 (some 247)) else d116 (change p 10000 (some 247))) = d8029 p
  rw [sub14133, sub13904]
  rfl
theorem sub14135 (p : Pattern) : d2126 (change p 10000 (some 247)) = d8030 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d2125 (change p 10000 (some 247))) = d8030 p
  rw [sub13654, sub13941]
  rfl
theorem sub14136 (p : Pattern) : d3178 (change p 10000 (some 247)) = d8031 p := by
  change (if p 182 then d2126 (change p 10000 (some 247)) else d3177 (change p 10000 (some 247))) = d8031 p
  rw [sub14135, sub14134]
  rfl
theorem sub14137 (p : Pattern) : d3179 (change p 10000 (some 247)) = d8032 p := by
  change (if p 163 then d3178 (change p 10000 (some 247)) else d3161 (change p 10000 (some 247))) = d8032 p
  rw [sub14136, sub14118]
  rfl
theorem sub14138 (p : Pattern) : d2135 (change p 10000 (some 247)) = d7681 p := by
  change (if p 225 then d1961 (change p 10000 (some 247)) else d1964 (change p 10000 (some 247))) = d7681 p
  rw [sub13927, sub13880]
  rfl
theorem sub14139 (p : Pattern) : d2136 (change p 10000 (some 247)) = d8033 p := by
  change (if p 224 then d2135 (change p 10000 (some 247)) else d1962 (change p 10000 (some 247))) = d8033 p
  rw [sub14138, sub13928]
  rfl
theorem sub14140 (p : Pattern) : d3180 (change p 10000 (some 247)) = d8034 p := by
  change (if p 204 then d2136 (change p 10000 (some 247)) else d107 (change p 10000 (some 247))) = d8034 p
  rw [sub14139, sub13878]
  rfl
theorem sub14141 (p : Pattern) : d2131 (change p 10000 (some 247)) = d8035 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d2130 (change p 10000 (some 247))) = d8035 p
  rw [sub13654, sub13882]
  rfl
theorem sub14142 (p : Pattern) : d3181 (change p 10000 (some 247)) = d8036 p := by
  change (if p 182 then d2131 (change p 10000 (some 247)) else d3180 (change p 10000 (some 247))) = d8036 p
  rw [sub14141, sub14140]
  rfl
theorem sub14143 (p : Pattern) : d3182 (change p 10000 (some 247)) = d8037 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d3181 (change p 10000 (some 247))) = d8037 p
  rw [sub13654, sub14142]
  rfl
theorem sub14144 (p : Pattern) : d3183 (change p 10000 (some 247)) = d8038 p := by
  change (if p 162 then d3182 (change p 10000 (some 247)) else d3179 (change p 10000 (some 247))) = d8038 p
  rw [sub14143, sub14137]
  rfl
theorem sub14145 (p : Pattern) : d2137 (change p 10000 (some 247)) = d8039 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d2136 (change p 10000 (some 247))) = d8039 p
  rw [sub13654, sub14139]
  rfl
theorem sub14146 (p : Pattern) : d3184 (change p 10000 (some 247)) = d8040 p := by
  change (if p 182 then d2137 (change p 10000 (some 247)) else d3007 (change p 10000 (some 247))) = d8040 p
  rw [sub14145, sub13932]
  rfl
theorem sub14147 (p : Pattern) : d3185 (change p 10000 (some 247)) = d8041 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d3184 (change p 10000 (some 247))) = d8041 p
  rw [sub13654, sub14146]
  rfl
theorem sub14148 (p : Pattern) : d3186 (change p 10000 (some 247)) = d8042 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d3185 (change p 10000 (some 247))) = d8042 p
  rw [sub13654, sub14147]
  rfl
theorem sub14149 (p : Pattern) : d3187 (change p 10000 (some 247)) = d8043 p := by
  change (if p 161 then d3186 (change p 10000 (some 247)) else d3183 (change p 10000 (some 247))) = d8043 p
  rw [sub14148, sub14144]
  rfl
theorem sub14150 (p : Pattern) : d3188 (change p 10000 (some 247)) = d8044 p := by
  change (if p 182 then d1906 (change p 10000 (some 247)) else d3007 (change p 10000 (some 247))) = d8044 p
  rw [sub13922, sub13932]
  rfl
theorem sub14151 (p : Pattern) : d3189 (change p 10000 (some 247)) = d8045 p := by
  change (if p 163 then d3008 (change p 10000 (some 247)) else d3188 (change p 10000 (some 247))) = d8045 p
  rw [sub13933, sub14150]
  rfl
theorem sub14152 (p : Pattern) : d3190 (change p 10000 (some 247)) = d8046 p := by
  change (if p 162 then d3171 (change p 10000 (some 247)) else d3189 (change p 10000 (some 247))) = d8046 p
  rw [sub14128, sub14151]
  rfl
theorem sub14153 (p : Pattern) : d3191 (change p 10000 (some 247)) = d8047 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d2918 (change p 10000 (some 247))) = d8047 p
  rw [sub13654, sub13758]
  rfl
theorem sub14154 (p : Pattern) : d3192 (change p 10000 (some 247)) = d8048 p := by
  change (if p 161 then d3191 (change p 10000 (some 247)) else d3190 (change p 10000 (some 247))) = d8048 p
  rw [sub14153, sub14152]
  rfl
theorem sub14155 (p : Pattern) : d3193 (change p 10000 (some 247)) = d8049 p := by
  change (if p 160 then d3192 (change p 10000 (some 247)) else d3187 (change p 10000 (some 247))) = d8049 p
  rw [sub14154, sub14149]
  rfl
theorem sub14156 (p : Pattern) : d3194 (change p 10000 (some 247)) = d8050 p := by
  change (if p 141 then d3193 (change p 10000 (some 247)) else d3174 (change p 10000 (some 247))) = d8050 p
  rw [sub14155, sub14131]
  rfl
theorem sub14157 (p : Pattern) : d3195 (change p 10000 (some 247)) = d8051 p := by
  change (if p 163 then d3042 (change p 10000 (some 247)) else d3040 (change p 10000 (some 247))) = d8051 p
  rw [sub13983, sub13980]
  rfl
theorem sub14158 (p : Pattern) : d3196 (change p 10000 (some 247)) = d8052 p := by
  change (if p 163 then d2931 (change p 10000 (some 247)) else d3048 (change p 10000 (some 247))) = d8052 p
  rw [sub13783, sub13990]
  rfl
theorem sub14159 (p : Pattern) : d3197 (change p 10000 (some 247)) = d8053 p := by
  change (if p 162 then d3196 (change p 10000 (some 247)) else d3195 (change p 10000 (some 247))) = d8053 p
  rw [sub14158, sub14157]
  rfl
end NetHack.Sokoban22Refined85
