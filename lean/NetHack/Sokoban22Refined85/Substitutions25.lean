/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions24
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub3000 (p : Pattern) : d73 (change p 115 none) = d73 p := by
  change (if p 163 then d12 (change p 115 none) else d72 (change p 115 none)) = d73 p
  rw [sub2933, sub2999]
  rfl
theorem sub3001 (p : Pattern) : d74 (change p 115 none) = d74 p := by
  change (if p 162 then d73 (change p 115 none) else d71 (change p 115 none)) = d74 p
  rw [sub3000, sub2998]
  rfl
theorem sub3002 (p : Pattern) : d75 (change p 115 none) = d75 p := by
  change (if p 161 then d74 (change p 115 none) else d69 (change p 115 none)) = d75 p
  rw [sub3001, sub2996]
  rfl
theorem sub3003 (p : Pattern) : d76 (change p 115 none) = d76 p := by
  change (if p 160 then d75 (change p 115 none) else d65 (change p 115 none)) = d76 p
  rw [sub3002, sub2992]
  rfl
theorem sub3004 (p : Pattern) : d77 (change p 115 none) = d77 p := by
  change (if p 141 then d76 (change p 115 none) else d52 (change p 115 none)) = d77 p
  rw [sub3003, sub2978]
  rfl
theorem sub3005 (p : Pattern) : d78 (change p 115 none) = d78 p := by
  change (if p 182 then d36 (change p 115 none) else d35 (change p 115 none)) = d78 p
  rw [sub2961, sub2960]
  rfl
theorem sub3006 (p : Pattern) : d79 (change p 115 none) = d79 p := by
  change (if p 163 then d78 (change p 115 none) else d53 (change p 115 none)) = d79 p
  rw [sub3005, sub2979]
  rfl
theorem sub3007 (p : Pattern) : d80 (change p 115 none) = d80 p := by
  change (if p 162 then d63 (change p 115 none) else d79 (change p 115 none)) = d80 p
  rw [sub2990, sub3006]
  rfl
theorem sub3008 (p : Pattern) : d81 (change p 115 none) = d81 p := by
  change (if p 161 then d12 (change p 115 none) else d80 (change p 115 none)) = d81 p
  rw [sub2933, sub3007]
  rfl
theorem sub3009 (p : Pattern) : d82 (change p 115 none) = d82 p := by
  change (if p 160 then d81 (change p 115 none) else d29 (change p 115 none)) = d82 p
  rw [sub3008, sub2952]
  rfl
theorem sub3010 (p : Pattern) : d83 (change p 115 none) = d83 p := by
  change (if p 163 then d12 (change p 115 none) else d78 (change p 115 none)) = d83 p
  rw [sub2933, sub3005]
  rfl
theorem sub3011 (p : Pattern) : d84 (change p 115 none) = d84 p := by
  change (if p 162 then d12 (change p 115 none) else d83 (change p 115 none)) = d84 p
  rw [sub2933, sub3010]
  rfl
theorem sub3012 (p : Pattern) : d85 (change p 115 none) = d85 p := by
  change (if p 161 then d12 (change p 115 none) else d84 (change p 115 none)) = d85 p
  rw [sub2933, sub3011]
  rfl
theorem sub3013 (p : Pattern) : d86 (change p 115 none) = d86 p := by
  change (if p 160 then d85 (change p 115 none) else d65 (change p 115 none)) = d86 p
  rw [sub3012, sub2992]
  rfl
theorem sub3014 (p : Pattern) : d87 (change p 115 none) = d87 p := by
  change (if p 141 then d86 (change p 115 none) else d82 (change p 115 none)) = d87 p
  rw [sub3013, sub3009]
  rfl
theorem sub3015 (p : Pattern) : d88 (change p 115 none) = d88 p := by
  change (if p 138 then d87 (change p 115 none) else d77 (change p 115 none)) = d88 p
  rw [sub3014, sub3004]
  rfl
theorem sub3016 (p : Pattern) : d89 (change p 115 none) = d89 p := by
  change (if p 163 then d62 (change p 115 none) else d26 (change p 115 none)) = d89 p
  rw [sub2989, sub2949]
  rfl
theorem sub3017 (p : Pattern) : d90 (change p 115 none) = d90 p := by
  change (if p 162 then d63 (change p 115 none) else d89 (change p 115 none)) = d90 p
  rw [sub2990, sub3016]
  rfl
theorem sub3018 (p : Pattern) : d91 (change p 115 none) = d91 p := by
  change (if p 162 then d12 (change p 115 none) else d63 (change p 115 none)) = d91 p
  rw [sub2933, sub2990]
  rfl
theorem sub3019 (p : Pattern) : d92 (change p 115 none) = d92 p := by
  change (if p 161 then d91 (change p 115 none) else d90 (change p 115 none)) = d92 p
  rw [sub3018, sub3017]
  rfl
theorem sub3020 (p : Pattern) : d93 (change p 115 none) = d93 p := by
  change (if p 161 then d12 (change p 115 none) else d91 (change p 115 none)) = d93 p
  rw [sub2933, sub3018]
  rfl
theorem sub3021 (p : Pattern) : d94 (change p 115 none) = d94 p := by
  change (if p 160 then d93 (change p 115 none) else d92 (change p 115 none)) = d94 p
  rw [sub3020, sub3019]
  rfl
theorem sub3022 (p : Pattern) : d95 (change p 115 none) = d95 p := by
  change (if p 160 then d12 (change p 115 none) else d93 (change p 115 none)) = d95 p
  rw [sub2933, sub3020]
  rfl
theorem sub3023 (p : Pattern) : d96 (change p 115 none) = d96 p := by
  change (if p 141 then d95 (change p 115 none) else d94 (change p 115 none)) = d96 p
  rw [sub3022, sub3021]
  rfl
theorem sub3024 (p : Pattern) : d97 (change p 115 none) = d97 p := by
  change (if p 138 then d96 (change p 115 none) else d87 (change p 115 none)) = d97 p
  rw [sub3023, sub3014]
  rfl
theorem sub3025 (p : Pattern) : d98 (change p 115 none) = d98 p := by
  change (if p 116 then d97 (change p 115 none) else d88 (change p 115 none)) = d98 p
  rw [sub3024, sub3015]
  rfl
theorem sub3026 (p : Pattern) : d489 (change p 115 none) = d98 p := by
  change d98 (change p 115 none) = d98 p
  exact sub3025 p
theorem sub3027 (p : Pattern) : d490 (change p 115 none) = d98 p := by
  change d98 (change p 115 none) = d98 p
  exact sub3025 p
theorem sub3028 (p : Pattern) : d491 (change p 115 none) = d98 p := by
  change (if p 71 then d490 (change p 115 none) else d489 (change p 115 none)) = d98 p
  rw [sub3027, sub3026]
  simp only [ite_self]
theorem sub3029 (p : Pattern) : d1 (change p 115 none) = d1 p := by
  rfl
theorem sub3030 (p : Pattern) : d102 (change p 115 none) = d102 p := by
  change (if p 247 then d12 (change p 115 none) else d1 (change p 115 none)) = d102 p
  rw [sub2933, sub3029]
  rfl
theorem sub3031 (p : Pattern) : d103 (change p 115 none) = d103 p := by
  change (if p 246 then d102 (change p 115 none) else d1 (change p 115 none)) = d103 p
  rw [sub3030, sub3029]
  rfl
theorem sub3032 (p : Pattern) : d104 (change p 115 none) = d104 p := by
  change (if p 204 then d12 (change p 115 none) else d103 (change p 115 none)) = d104 p
  rw [sub2933, sub3031]
  rfl
theorem sub3033 (p : Pattern) : d105 (change p 115 none) = d105 p := by
  change (if p 182 then d104 (change p 115 none) else d103 (change p 115 none)) = d105 p
  rw [sub3032, sub3031]
  rfl
theorem sub3034 (p : Pattern) : d5 (change p 115 none) = d5 p := by
  rfl
theorem sub3035 (p : Pattern) : d106 (change p 115 none) = d106 p := by
  change (if p 247 then d12 (change p 115 none) else d5 (change p 115 none)) = d106 p
  rw [sub2933, sub3034]
  rfl
theorem sub3036 (p : Pattern) : d107 (change p 115 none) = d107 p := by
  change (if p 246 then d106 (change p 115 none) else d5 (change p 115 none)) = d107 p
  rw [sub3035, sub3034]
  rfl
theorem sub3037 (p : Pattern) : d108 (change p 115 none) = d108 p := by
  change (if p 204 then d12 (change p 115 none) else d107 (change p 115 none)) = d108 p
  rw [sub2933, sub3036]
  rfl
theorem sub3038 (p : Pattern) : d109 (change p 115 none) = d109 p := by
  change (if p 182 then d108 (change p 115 none) else d107 (change p 115 none)) = d109 p
  rw [sub3037, sub3036]
  rfl
theorem sub3039 (p : Pattern) : d110 (change p 115 none) = d110 p := by
  change (if p 163 then d109 (change p 115 none) else d105 (change p 115 none)) = d110 p
  rw [sub3038, sub3033]
  rfl
theorem sub3040 (p : Pattern) : d111 (change p 115 none) = d111 p := by
  change (if p 162 then d110 (change p 115 none) else d105 (change p 115 none)) = d111 p
  rw [sub3039, sub3033]
  rfl
theorem sub3041 (p : Pattern) : d112 (change p 115 none) = d112 p := by
  change (if p 163 then d12 (change p 115 none) else d60 (change p 115 none)) = d112 p
  rw [sub2933, sub2987]
  rfl
theorem sub3042 (p : Pattern) : d113 (change p 115 none) = d113 p := by
  change (if p 162 then d112 (change p 115 none) else d110 (change p 115 none)) = d113 p
  rw [sub3041, sub3039]
  rfl
theorem sub3043 (p : Pattern) : d114 (change p 115 none) = d114 p := by
  change (if p 161 then d113 (change p 115 none) else d111 (change p 115 none)) = d114 p
  rw [sub3042, sub3040]
  rfl
theorem sub3044 (p : Pattern) : d3 (change p 115 none) = d3 p := by
  rfl
theorem sub3045 (p : Pattern) : d115 (change p 115 none) = d115 p := by
  change (if p 247 then d12 (change p 115 none) else d3 (change p 115 none)) = d115 p
  rw [sub2933, sub3044]
  rfl
theorem sub3046 (p : Pattern) : d116 (change p 115 none) = d116 p := by
  change (if p 246 then d115 (change p 115 none) else d3 (change p 115 none)) = d116 p
  rw [sub3045, sub3044]
  rfl
theorem sub3047 (p : Pattern) : d117 (change p 115 none) = d117 p := by
  change (if p 204 then d12 (change p 115 none) else d116 (change p 115 none)) = d117 p
  rw [sub2933, sub3046]
  rfl
theorem sub3048 (p : Pattern) : d118 (change p 115 none) = d118 p := by
  change (if p 182 then d117 (change p 115 none) else d103 (change p 115 none)) = d118 p
  rw [sub3047, sub3031]
  rfl
theorem sub3049 (p : Pattern) : d7 (change p 115 none) = d7 p := by
  rfl
theorem sub3050 (p : Pattern) : d119 (change p 115 none) = d119 p := by
  change (if p 247 then d12 (change p 115 none) else d7 (change p 115 none)) = d119 p
  rw [sub2933, sub3049]
  rfl
theorem sub3051 (p : Pattern) : d120 (change p 115 none) = d120 p := by
  change (if p 246 then d119 (change p 115 none) else d7 (change p 115 none)) = d120 p
  rw [sub3050, sub3049]
  rfl
theorem sub3052 (p : Pattern) : d121 (change p 115 none) = d121 p := by
  change (if p 204 then d12 (change p 115 none) else d120 (change p 115 none)) = d121 p
  rw [sub2933, sub3051]
  rfl
theorem sub3053 (p : Pattern) : d122 (change p 115 none) = d122 p := by
  change (if p 182 then d121 (change p 115 none) else d103 (change p 115 none)) = d122 p
  rw [sub3052, sub3031]
  rfl
theorem sub3054 (p : Pattern) : d123 (change p 115 none) = d123 p := by
  change (if p 163 then d122 (change p 115 none) else d118 (change p 115 none)) = d123 p
  rw [sub3053, sub3048]
  rfl
theorem sub3055 (p : Pattern) : d124 (change p 115 none) = d124 p := by
  change (if p 182 then d12 (change p 115 none) else d103 (change p 115 none)) = d124 p
  rw [sub2933, sub3031]
  rfl
theorem sub3056 (p : Pattern) : d125 (change p 115 none) = d125 p := by
  change (if p 182 then d12 (change p 115 none) else d107 (change p 115 none)) = d125 p
  rw [sub2933, sub3036]
  rfl
theorem sub3057 (p : Pattern) : d126 (change p 115 none) = d126 p := by
  change (if p 163 then d125 (change p 115 none) else d124 (change p 115 none)) = d126 p
  rw [sub3056, sub3055]
  rfl
theorem sub3058 (p : Pattern) : d127 (change p 115 none) = d127 p := by
  change (if p 162 then d126 (change p 115 none) else d123 (change p 115 none)) = d127 p
  rw [sub3057, sub3054]
  rfl
theorem sub3059 (p : Pattern) : d128 (change p 115 none) = d128 p := by
  change (if p 163 then d12 (change p 115 none) else d70 (change p 115 none)) = d128 p
  rw [sub2933, sub2997]
  rfl
theorem sub3060 (p : Pattern) : d129 (change p 115 none) = d129 p := by
  change (if p 162 then d128 (change p 115 none) else d126 (change p 115 none)) = d129 p
  rw [sub3059, sub3057]
  rfl
theorem sub3061 (p : Pattern) : d130 (change p 115 none) = d130 p := by
  change (if p 161 then d129 (change p 115 none) else d127 (change p 115 none)) = d130 p
  rw [sub3060, sub3058]
  rfl
theorem sub3062 (p : Pattern) : d131 (change p 115 none) = d131 p := by
  change (if p 160 then d130 (change p 115 none) else d114 (change p 115 none)) = d131 p
  rw [sub3061, sub3043]
  rfl
theorem sub3063 (p : Pattern) : d132 (change p 115 none) = d132 p := by
  change (if p 182 then d117 (change p 115 none) else d116 (change p 115 none)) = d132 p
  rw [sub3047, sub3046]
  rfl
theorem sub3064 (p : Pattern) : d133 (change p 115 none) = d133 p := by
  change (if p 163 then d132 (change p 115 none) else d105 (change p 115 none)) = d133 p
  rw [sub3063, sub3033]
  rfl
theorem sub3065 (p : Pattern) : d134 (change p 115 none) = d134 p := by
  change (if p 163 then d60 (change p 115 none) else d109 (change p 115 none)) = d134 p
  rw [sub2987, sub3038]
  rfl
theorem sub3066 (p : Pattern) : d135 (change p 115 none) = d135 p := by
  change (if p 162 then d134 (change p 115 none) else d133 (change p 115 none)) = d135 p
  rw [sub3065, sub3064]
  rfl
theorem sub3067 (p : Pattern) : d136 (change p 115 none) = d136 p := by
  change (if p 163 then d62 (change p 115 none) else d109 (change p 115 none)) = d136 p
  rw [sub2989, sub3038]
  rfl
theorem sub3068 (p : Pattern) : d137 (change p 115 none) = d137 p := by
  change (if p 162 then d12 (change p 115 none) else d136 (change p 115 none)) = d137 p
  rw [sub2933, sub3067]
  rfl
theorem sub3069 (p : Pattern) : d138 (change p 115 none) = d138 p := by
  change (if p 161 then d137 (change p 115 none) else d135 (change p 115 none)) = d138 p
  rw [sub3068, sub3066]
  rfl
theorem sub3070 (p : Pattern) : d139 (change p 115 none) = d139 p := by
  change (if p 182 then d12 (change p 115 none) else d116 (change p 115 none)) = d139 p
  rw [sub2933, sub3046]
  rfl
theorem sub3071 (p : Pattern) : d140 (change p 115 none) = d140 p := by
  change (if p 163 then d139 (change p 115 none) else d122 (change p 115 none)) = d140 p
  rw [sub3070, sub3053]
  rfl
theorem sub3072 (p : Pattern) : d141 (change p 115 none) = d141 p := by
  change (if p 163 then d70 (change p 115 none) else d125 (change p 115 none)) = d141 p
  rw [sub2997, sub3056]
  rfl
theorem sub3073 (p : Pattern) : d142 (change p 115 none) = d142 p := by
  change (if p 162 then d141 (change p 115 none) else d140 (change p 115 none)) = d142 p
  rw [sub3072, sub3071]
  rfl
theorem sub3074 (p : Pattern) : d143 (change p 115 none) = d143 p := by
  change (if p 163 then d72 (change p 115 none) else d125 (change p 115 none)) = d143 p
  rw [sub2999, sub3056]
  rfl
theorem sub3075 (p : Pattern) : d144 (change p 115 none) = d144 p := by
  change (if p 162 then d12 (change p 115 none) else d143 (change p 115 none)) = d144 p
  rw [sub2933, sub3074]
  rfl
theorem sub3076 (p : Pattern) : d145 (change p 115 none) = d145 p := by
  change (if p 161 then d144 (change p 115 none) else d142 (change p 115 none)) = d145 p
  rw [sub3075, sub3073]
  rfl
theorem sub3077 (p : Pattern) : d146 (change p 115 none) = d146 p := by
  change (if p 160 then d145 (change p 115 none) else d138 (change p 115 none)) = d146 p
  rw [sub3076, sub3069]
  rfl
theorem sub3078 (p : Pattern) : d147 (change p 115 none) = d147 p := by
  change (if p 141 then d146 (change p 115 none) else d131 (change p 115 none)) = d147 p
  rw [sub3077, sub3062]
  rfl
theorem sub3079 (p : Pattern) : d148 (change p 115 none) = d148 p := by
  change (if p 182 then d121 (change p 115 none) else d120 (change p 115 none)) = d148 p
  rw [sub3052, sub3051]
  rfl
theorem sub3080 (p : Pattern) : d149 (change p 115 none) = d149 p := by
  change (if p 163 then d148 (change p 115 none) else d132 (change p 115 none)) = d149 p
  rw [sub3079, sub3063]
  rfl
theorem sub3081 (p : Pattern) : d150 (change p 115 none) = d150 p := by
  change (if p 162 then d12 (change p 115 none) else d149 (change p 115 none)) = d150 p
  rw [sub2933, sub3080]
  rfl
theorem sub3082 (p : Pattern) : d151 (change p 115 none) = d151 p := by
  change (if p 161 then d12 (change p 115 none) else d150 (change p 115 none)) = d151 p
  rw [sub2933, sub3081]
  rfl
theorem sub3083 (p : Pattern) : d152 (change p 115 none) = d152 p := by
  change (if p 160 then d151 (change p 115 none) else d114 (change p 115 none)) = d152 p
  rw [sub3082, sub3043]
  rfl
theorem sub3084 (p : Pattern) : d153 (change p 115 none) = d153 p := by
  change (if p 163 then d12 (change p 115 none) else d148 (change p 115 none)) = d153 p
  rw [sub2933, sub3079]
  rfl
theorem sub3085 (p : Pattern) : d154 (change p 115 none) = d154 p := by
  change (if p 162 then d12 (change p 115 none) else d153 (change p 115 none)) = d154 p
  rw [sub2933, sub3084]
  rfl
theorem sub3086 (p : Pattern) : d155 (change p 115 none) = d155 p := by
  change (if p 161 then d12 (change p 115 none) else d154 (change p 115 none)) = d155 p
  rw [sub2933, sub3085]
  rfl
theorem sub3087 (p : Pattern) : d156 (change p 115 none) = d156 p := by
  change (if p 160 then d155 (change p 115 none) else d138 (change p 115 none)) = d156 p
  rw [sub3086, sub3069]
  rfl
theorem sub3088 (p : Pattern) : d157 (change p 115 none) = d157 p := by
  change (if p 141 then d156 (change p 115 none) else d152 (change p 115 none)) = d157 p
  rw [sub3087, sub3083]
  rfl
theorem sub3089 (p : Pattern) : d158 (change p 115 none) = d158 p := by
  change (if p 138 then d157 (change p 115 none) else d147 (change p 115 none)) = d158 p
  rw [sub3088, sub3078]
  rfl
theorem sub3090 (p : Pattern) : d159 (change p 115 none) = d159 p := by
  change (if p 162 then d12 (change p 115 none) else d112 (change p 115 none)) = d159 p
  rw [sub2933, sub3041]
  rfl
theorem sub3091 (p : Pattern) : d160 (change p 115 none) = d160 p := by
  change (if p 161 then d12 (change p 115 none) else d159 (change p 115 none)) = d160 p
  rw [sub2933, sub3090]
  rfl
theorem sub3092 (p : Pattern) : d161 (change p 115 none) = d161 p := by
  change (if p 160 then d12 (change p 115 none) else d160 (change p 115 none)) = d161 p
  rw [sub2933, sub3091]
  rfl
theorem sub3093 (p : Pattern) : d162 (change p 115 none) = d162 p := by
  change (if p 141 then d12 (change p 115 none) else d161 (change p 115 none)) = d162 p
  rw [sub2933, sub3092]
  rfl
theorem sub3094 (p : Pattern) : d163 (change p 115 none) = d163 p := by
  change (if p 138 then d162 (change p 115 none) else d157 (change p 115 none)) = d163 p
  rw [sub3093, sub3088]
  rfl
theorem sub3095 (p : Pattern) : d164 (change p 115 none) = d164 p := by
  change (if p 116 then d163 (change p 115 none) else d158 (change p 115 none)) = d164 p
  rw [sub3094, sub3089]
  rfl
theorem sub3096 (p : Pattern) : d492 (change p 115 none) = d164 p := by
  change d164 (change p 115 none) = d164 p
  exact sub3095 p
theorem sub3097 (p : Pattern) : d493 (change p 115 none) = d4142 p := by
  change (if p 71 then d492 (change p 115 none) else d489 (change p 115 none)) = d4142 p
  rw [sub3096, sub3026]
  rfl
theorem sub3098 (p : Pattern) : d494 (change p 115 none) = d4143 p := by
  change (if p 49 then d493 (change p 115 none) else d491 (change p 115 none)) = d4143 p
  rw [sub3097, sub3028]
  rfl
theorem sub3099 (p : Pattern) : d211 (change p 115 none) = d211 p := by
  change (if p 163 then d12 (change p 115 none) else d109 (change p 115 none)) = d211 p
  rw [sub2933, sub3038]
  rfl
theorem sub3100 (p : Pattern) : d212 (change p 115 none) = d212 p := by
  change (if p 162 then d211 (change p 115 none) else d133 (change p 115 none)) = d212 p
  rw [sub3099, sub3064]
  rfl
theorem sub3101 (p : Pattern) : d213 (change p 115 none) = d213 p := by
  change (if p 162 then d12 (change p 115 none) else d211 (change p 115 none)) = d213 p
  rw [sub2933, sub3099]
  rfl
theorem sub3102 (p : Pattern) : d214 (change p 115 none) = d214 p := by
  change (if p 161 then d213 (change p 115 none) else d212 (change p 115 none)) = d214 p
  rw [sub3101, sub3100]
  rfl
theorem sub3103 (p : Pattern) : d215 (change p 115 none) = d215 p := by
  change (if p 163 then d12 (change p 115 none) else d125 (change p 115 none)) = d215 p
  rw [sub2933, sub3056]
  rfl
theorem sub3104 (p : Pattern) : d216 (change p 115 none) = d216 p := by
  change (if p 162 then d215 (change p 115 none) else d140 (change p 115 none)) = d216 p
  rw [sub3103, sub3071]
  rfl
theorem sub3105 (p : Pattern) : d217 (change p 115 none) = d217 p := by
  change (if p 162 then d12 (change p 115 none) else d215 (change p 115 none)) = d217 p
  rw [sub2933, sub3103]
  rfl
theorem sub3106 (p : Pattern) : d218 (change p 115 none) = d218 p := by
  change (if p 161 then d217 (change p 115 none) else d216 (change p 115 none)) = d218 p
  rw [sub3105, sub3104]
  rfl
theorem sub3107 (p : Pattern) : d219 (change p 115 none) = d219 p := by
  change (if p 160 then d218 (change p 115 none) else d214 (change p 115 none)) = d219 p
  rw [sub3106, sub3102]
  rfl
theorem sub3108 (p : Pattern) : d220 (change p 115 none) = d220 p := by
  change (if p 141 then d219 (change p 115 none) else d131 (change p 115 none)) = d220 p
  rw [sub3107, sub3062]
  rfl
theorem sub3109 (p : Pattern) : d221 (change p 115 none) = d221 p := by
  change (if p 160 then d155 (change p 115 none) else d214 (change p 115 none)) = d221 p
  rw [sub3086, sub3102]
  rfl
theorem sub3110 (p : Pattern) : d222 (change p 115 none) = d222 p := by
  change (if p 141 then d221 (change p 115 none) else d152 (change p 115 none)) = d222 p
  rw [sub3109, sub3083]
  rfl
theorem sub3111 (p : Pattern) : d223 (change p 115 none) = d223 p := by
  change (if p 138 then d222 (change p 115 none) else d220 (change p 115 none)) = d223 p
  rw [sub3110, sub3108]
  rfl
theorem sub3112 (p : Pattern) : d224 (change p 115 none) = d224 p := by
  change (if p 138 then d162 (change p 115 none) else d222 (change p 115 none)) = d224 p
  rw [sub3093, sub3110]
  rfl
theorem sub3113 (p : Pattern) : d225 (change p 115 none) = d225 p := by
  change (if p 116 then d224 (change p 115 none) else d223 (change p 115 none)) = d225 p
  rw [sub3112, sub3111]
  rfl
theorem sub3114 (p : Pattern) : d495 (change p 115 none) = d225 p := by
  change d225 (change p 115 none) = d225 p
  exact sub3113 p
theorem sub3115 (p : Pattern) : d496 (change p 115 none) = d4144 p := by
  change (if p 71 then d495 (change p 115 none) else d489 (change p 115 none)) = d4144 p
  rw [sub3114, sub3026]
  rfl
theorem sub3116 (p : Pattern) : d497 (change p 115 none) = d4145 p := by
  change (if p 49 then d496 (change p 115 none) else d491 (change p 115 none)) = d4145 p
  rw [sub3115, sub3028]
  rfl
theorem sub3117 (p : Pattern) : d498 (change p 115 none) = d4146 p := by
  change (if p 48 then d497 (change p 115 none) else d494 (change p 115 none)) = d4146 p
  rw [sub3116, sub3098]
  rfl
theorem sub3118 (p : Pattern) : d0 (change p 141 (some 163)) = d0 p := by
  rfl
theorem sub3119 (p : Pattern) : d12 (change p 141 (some 163)) = d12 p := by
  rfl
end NetHack.Sokoban22Refined85
