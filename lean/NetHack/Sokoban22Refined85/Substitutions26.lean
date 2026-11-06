/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions25
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub3120 (p : Pattern) : d13 (change p 141 (some 163)) = d13 p := by
  change (if p 247 then d12 (change p 141 (some 163)) else d0 (change p 141 (some 163))) = d13 p
  rw [sub3119, sub3118]
  rfl
theorem sub3121 (p : Pattern) : d14 (change p 141 (some 163)) = d14 p := by
  change (if p 246 then d13 (change p 141 (some 163)) else d0 (change p 141 (some 163))) = d14 p
  rw [sub3120, sub3118]
  rfl
theorem sub3122 (p : Pattern) : d15 (change p 141 (some 163)) = d15 p := by
  change (if p 204 then d12 (change p 141 (some 163)) else d14 (change p 141 (some 163))) = d15 p
  rw [sub3119, sub3121]
  rfl
theorem sub3123 (p : Pattern) : d16 (change p 141 (some 163)) = d16 p := by
  change (if p 182 then d15 (change p 141 (some 163)) else d14 (change p 141 (some 163))) = d16 p
  rw [sub3122, sub3121]
  rfl
theorem sub3124 (p : Pattern) : d4 (change p 141 (some 163)) = d4 p := by
  rfl
theorem sub3125 (p : Pattern) : d17 (change p 141 (some 163)) = d17 p := by
  change (if p 247 then d12 (change p 141 (some 163)) else d4 (change p 141 (some 163))) = d17 p
  rw [sub3119, sub3124]
  rfl
theorem sub3126 (p : Pattern) : d18 (change p 141 (some 163)) = d18 p := by
  change (if p 246 then d17 (change p 141 (some 163)) else d4 (change p 141 (some 163))) = d18 p
  rw [sub3125, sub3124]
  rfl
theorem sub3127 (p : Pattern) : d19 (change p 141 (some 163)) = d19 p := by
  change (if p 204 then d12 (change p 141 (some 163)) else d18 (change p 141 (some 163))) = d19 p
  rw [sub3119, sub3126]
  rfl
theorem sub3128 (p : Pattern) : d20 (change p 141 (some 163)) = d20 p := by
  change (if p 182 then d19 (change p 141 (some 163)) else d18 (change p 141 (some 163))) = d20 p
  rw [sub3127, sub3126]
  rfl
theorem sub3129 (p : Pattern) : d21 (change p 141 (some 163)) = d20 p := by
  change d20 (change p 141 (some 163)) = d20 p
  exact sub3128 p
theorem sub3130 (p : Pattern) : d22 (change p 141 (some 163)) = d4150 p := by
  change (if p 162 then d21 (change p 141 (some 163)) else d16 (change p 141 (some 163))) = d4150 p
  rw [sub3129, sub3123]
  rfl
theorem sub3131 (p : Pattern) : d27 (change p 141 (some 163)) = d12 p := by
  change d12 (change p 141 (some 163)) = d12 p
  exact sub3119 p
theorem sub3132 (p : Pattern) : d28 (change p 141 (some 163)) = d1100 p := by
  change (if p 162 then d27 (change p 141 (some 163)) else d21 (change p 141 (some 163))) = d1100 p
  rw [sub3131, sub3129]
  rfl
theorem sub3133 (p : Pattern) : d29 (change p 141 (some 163)) = d4151 p := by
  change (if p 161 then d28 (change p 141 (some 163)) else d22 (change p 141 (some 163))) = d4151 p
  rw [sub3132, sub3130]
  rfl
theorem sub3134 (p : Pattern) : d6 (change p 141 (some 163)) = d6 p := by
  rfl
theorem sub3135 (p : Pattern) : d34 (change p 141 (some 163)) = d34 p := by
  change (if p 247 then d12 (change p 141 (some 163)) else d6 (change p 141 (some 163))) = d34 p
  rw [sub3119, sub3134]
  rfl
theorem sub3136 (p : Pattern) : d35 (change p 141 (some 163)) = d35 p := by
  change (if p 246 then d34 (change p 141 (some 163)) else d6 (change p 141 (some 163))) = d35 p
  rw [sub3135, sub3134]
  rfl
theorem sub3137 (p : Pattern) : d36 (change p 141 (some 163)) = d36 p := by
  change (if p 204 then d12 (change p 141 (some 163)) else d35 (change p 141 (some 163))) = d36 p
  rw [sub3119, sub3136]
  rfl
theorem sub3138 (p : Pattern) : d37 (change p 141 (some 163)) = d37 p := by
  change (if p 182 then d36 (change p 141 (some 163)) else d14 (change p 141 (some 163))) = d37 p
  rw [sub3137, sub3121]
  rfl
theorem sub3139 (p : Pattern) : d38 (change p 141 (some 163)) = d37 p := by
  change d37 (change p 141 (some 163)) = d37 p
  exact sub3138 p
theorem sub3140 (p : Pattern) : d43 (change p 141 (some 163)) = d43 p := by
  change (if p 182 then d12 (change p 141 (some 163)) else d18 (change p 141 (some 163))) = d43 p
  rw [sub3119, sub3126]
  rfl
theorem sub3141 (p : Pattern) : d44 (change p 141 (some 163)) = d43 p := by
  change d43 (change p 141 (some 163)) = d43 p
  exact sub3140 p
theorem sub3142 (p : Pattern) : d45 (change p 141 (some 163)) = d4152 p := by
  change (if p 162 then d44 (change p 141 (some 163)) else d38 (change p 141 (some 163))) = d4152 p
  rw [sub3141, sub3139]
  rfl
theorem sub3143 (p : Pattern) : d47 (change p 141 (some 163)) = d43 p := by
  change d43 (change p 141 (some 163)) = d43 p
  exact sub3140 p
theorem sub3144 (p : Pattern) : d49 (change p 141 (some 163)) = d12 p := by
  change d12 (change p 141 (some 163)) = d12 p
  exact sub3119 p
theorem sub3145 (p : Pattern) : d50 (change p 141 (some 163)) = d4153 p := by
  change (if p 162 then d49 (change p 141 (some 163)) else d47 (change p 141 (some 163))) = d4153 p
  rw [sub3144, sub3143]
  rfl
theorem sub3146 (p : Pattern) : d51 (change p 141 (some 163)) = d4154 p := by
  change (if p 161 then d50 (change p 141 (some 163)) else d45 (change p 141 (some 163))) = d4154 p
  rw [sub3145, sub3142]
  rfl
theorem sub3147 (p : Pattern) : d52 (change p 141 (some 163)) = d4155 p := by
  change (if p 160 then d51 (change p 141 (some 163)) else d29 (change p 141 (some 163))) = d4155 p
  rw [sub3146, sub3133]
  rfl
theorem sub3148 (p : Pattern) : d653 (change p 141 (some 163)) = d4155 p := by
  change d52 (change p 141 (some 163)) = d4155 p
  exact sub3147 p
theorem sub3149 (p : Pattern) : d78 (change p 141 (some 163)) = d78 p := by
  change (if p 182 then d36 (change p 141 (some 163)) else d35 (change p 141 (some 163))) = d78 p
  rw [sub3137, sub3136]
  rfl
theorem sub3150 (p : Pattern) : d79 (change p 141 (some 163)) = d78 p := by
  change d78 (change p 141 (some 163)) = d78 p
  exact sub3149 p
theorem sub3151 (p : Pattern) : d63 (change p 141 (some 163)) = d12 p := by
  change d12 (change p 141 (some 163)) = d12 p
  exact sub3119 p
theorem sub3152 (p : Pattern) : d80 (change p 141 (some 163)) = d4156 p := by
  change (if p 162 then d63 (change p 141 (some 163)) else d79 (change p 141 (some 163))) = d4156 p
  rw [sub3151, sub3150]
  rfl
theorem sub3153 (p : Pattern) : d81 (change p 141 (some 163)) = d4157 p := by
  change (if p 161 then d12 (change p 141 (some 163)) else d80 (change p 141 (some 163))) = d4157 p
  rw [sub3119, sub3152]
  rfl
theorem sub3154 (p : Pattern) : d82 (change p 141 (some 163)) = d4158 p := by
  change (if p 160 then d81 (change p 141 (some 163)) else d29 (change p 141 (some 163))) = d4158 p
  rw [sub3153, sub3133]
  rfl
theorem sub3155 (p : Pattern) : d654 (change p 141 (some 163)) = d4158 p := by
  change d82 (change p 141 (some 163)) = d4158 p
  exact sub3154 p
theorem sub3156 (p : Pattern) : d655 (change p 141 (some 163)) = d4159 p := by
  change (if p 138 then d654 (change p 141 (some 163)) else d653 (change p 141 (some 163))) = d4159 p
  rw [sub3155, sub3148]
  rfl
theorem sub3157 (p : Pattern) : d656 (change p 141 (some 163)) = d4158 p := by
  change d82 (change p 141 (some 163)) = d4158 p
  exact sub3154 p
theorem sub3158 (p : Pattern) : d11 (change p 141 (some 163)) = d11 p := by
  rfl
theorem sub3159 (p : Pattern) : d39 (change p 141 (some 163)) = d39 p := by
  change (if p 247 then d12 (change p 141 (some 163)) else d11 (change p 141 (some 163))) = d39 p
  rw [sub3119, sub3158]
  rfl
theorem sub3160 (p : Pattern) : d40 (change p 141 (some 163)) = d40 p := by
  change (if p 246 then d39 (change p 141 (some 163)) else d11 (change p 141 (some 163))) = d40 p
  rw [sub3159, sub3158]
  rfl
theorem sub3161 (p : Pattern) : d41 (change p 141 (some 163)) = d41 p := by
  change (if p 204 then d12 (change p 141 (some 163)) else d40 (change p 141 (some 163))) = d41 p
  rw [sub3119, sub3160]
  rfl
theorem sub3162 (p : Pattern) : d62 (change p 141 (some 163)) = d62 p := by
  change (if p 182 then d41 (change p 141 (some 163)) else d40 (change p 141 (some 163))) = d62 p
  rw [sub3161, sub3160]
  rfl
theorem sub3163 (p : Pattern) : d89 (change p 141 (some 163)) = d62 p := by
  change d62 (change p 141 (some 163)) = d62 p
  exact sub3162 p
theorem sub3164 (p : Pattern) : d90 (change p 141 (some 163)) = d4160 p := by
  change (if p 162 then d63 (change p 141 (some 163)) else d89 (change p 141 (some 163))) = d4160 p
  rw [sub3151, sub3163]
  rfl
theorem sub3165 (p : Pattern) : d91 (change p 141 (some 163)) = d12 p := by
  change (if p 162 then d12 (change p 141 (some 163)) else d63 (change p 141 (some 163))) = d12 p
  rw [sub3119, sub3151]
  simp only [ite_self]
theorem sub3166 (p : Pattern) : d92 (change p 141 (some 163)) = d4161 p := by
  change (if p 161 then d91 (change p 141 (some 163)) else d90 (change p 141 (some 163))) = d4161 p
  rw [sub3165, sub3164]
  rfl
theorem sub3167 (p : Pattern) : d93 (change p 141 (some 163)) = d12 p := by
  change (if p 161 then d12 (change p 141 (some 163)) else d91 (change p 141 (some 163))) = d12 p
  rw [sub3119, sub3165]
  simp only [ite_self]
theorem sub3168 (p : Pattern) : d94 (change p 141 (some 163)) = d4162 p := by
  change (if p 160 then d93 (change p 141 (some 163)) else d92 (change p 141 (some 163))) = d4162 p
  rw [sub3167, sub3166]
  rfl
theorem sub3169 (p : Pattern) : d657 (change p 141 (some 163)) = d4162 p := by
  change d94 (change p 141 (some 163)) = d4162 p
  exact sub3168 p
theorem sub3170 (p : Pattern) : d658 (change p 141 (some 163)) = d4163 p := by
  change (if p 138 then d657 (change p 141 (some 163)) else d656 (change p 141 (some 163))) = d4163 p
  rw [sub3169, sub3157]
  rfl
theorem sub3171 (p : Pattern) : d659 (change p 141 (some 163)) = d4164 p := by
  change (if p 116 then d658 (change p 141 (some 163)) else d655 (change p 141 (some 163))) = d4164 p
  rw [sub3170, sub3156]
  rfl
theorem sub3172 (p : Pattern) : d660 (change p 141 (some 163)) = d4155 p := by
  change d52 (change p 141 (some 163)) = d4155 p
  exact sub3147 p
theorem sub3173 (p : Pattern) : d661 (change p 141 (some 163)) = d4158 p := by
  change d82 (change p 141 (some 163)) = d4158 p
  exact sub3154 p
theorem sub3174 (p : Pattern) : d662 (change p 141 (some 163)) = d4159 p := by
  change (if p 138 then d661 (change p 141 (some 163)) else d660 (change p 141 (some 163))) = d4159 p
  rw [sub3173, sub3172]
  rfl
theorem sub3175 (p : Pattern) : d663 (change p 141 (some 163)) = d4158 p := by
  change d82 (change p 141 (some 163)) = d4158 p
  exact sub3154 p
theorem sub3176 (p : Pattern) : d664 (change p 141 (some 163)) = d4165 p := by
  change (if p 138 then d12 (change p 141 (some 163)) else d663 (change p 141 (some 163))) = d4165 p
  rw [sub3119, sub3175]
  rfl
theorem sub3177 (p : Pattern) : d665 (change p 141 (some 163)) = d4166 p := by
  change (if p 116 then d664 (change p 141 (some 163)) else d662 (change p 141 (some 163))) = d4166 p
  rw [sub3176, sub3174]
  rfl
theorem sub3178 (p : Pattern) : d666 (change p 141 (some 163)) = d4167 p := by
  change (if p 115 then d665 (change p 141 (some 163)) else d659 (change p 141 (some 163))) = d4167 p
  rw [sub3177, sub3171]
  rfl
theorem sub3179 (p : Pattern) : d667 (change p 141 (some 163)) = d4155 p := by
  change d52 (change p 141 (some 163)) = d4155 p
  exact sub3147 p
theorem sub3180 (p : Pattern) : d668 (change p 141 (some 163)) = d4158 p := by
  change d82 (change p 141 (some 163)) = d4158 p
  exact sub3154 p
theorem sub3181 (p : Pattern) : d669 (change p 141 (some 163)) = d4159 p := by
  change (if p 138 then d668 (change p 141 (some 163)) else d667 (change p 141 (some 163))) = d4159 p
  rw [sub3180, sub3179]
  rfl
theorem sub3182 (p : Pattern) : d670 (change p 141 (some 163)) = d4162 p := by
  change d94 (change p 141 (some 163)) = d4162 p
  exact sub3168 p
theorem sub3183 (p : Pattern) : d671 (change p 141 (some 163)) = d4163 p := by
  change (if p 138 then d670 (change p 141 (some 163)) else d654 (change p 141 (some 163))) = d4163 p
  rw [sub3182, sub3155]
  rfl
theorem sub3184 (p : Pattern) : d672 (change p 141 (some 163)) = d4164 p := by
  change (if p 116 then d671 (change p 141 (some 163)) else d669 (change p 141 (some 163))) = d4164 p
  rw [sub3183, sub3181]
  rfl
theorem sub3185 (p : Pattern) : d673 (change p 141 (some 163)) = d4155 p := by
  change d52 (change p 141 (some 163)) = d4155 p
  exact sub3147 p
theorem sub3186 (p : Pattern) : d674 (change p 141 (some 163)) = d4158 p := by
  change d82 (change p 141 (some 163)) = d4158 p
  exact sub3154 p
theorem sub3187 (p : Pattern) : d675 (change p 141 (some 163)) = d4159 p := by
  change (if p 138 then d674 (change p 141 (some 163)) else d673 (change p 141 (some 163))) = d4159 p
  rw [sub3186, sub3185]
  rfl
theorem sub3188 (p : Pattern) : d676 (change p 141 (some 163)) = d4165 p := by
  change (if p 138 then d12 (change p 141 (some 163)) else d661 (change p 141 (some 163))) = d4165 p
  rw [sub3119, sub3173]
  rfl
theorem sub3189 (p : Pattern) : d677 (change p 141 (some 163)) = d4166 p := by
  change (if p 116 then d676 (change p 141 (some 163)) else d675 (change p 141 (some 163))) = d4166 p
  rw [sub3188, sub3187]
  rfl
theorem sub3190 (p : Pattern) : d678 (change p 141 (some 163)) = d4167 p := by
  change (if p 115 then d677 (change p 141 (some 163)) else d672 (change p 141 (some 163))) = d4167 p
  rw [sub3189, sub3184]
  rfl
theorem sub3191 (p : Pattern) : d679 (change p 141 (some 163)) = d4167 p := by
  change (if p 71 then d678 (change p 141 (some 163)) else d666 (change p 141 (some 163))) = d4167 p
  rw [sub3190, sub3178]
  simp only [ite_self]
theorem sub3192 (p : Pattern) : d1 (change p 141 (some 163)) = d1 p := by
  rfl
theorem sub3193 (p : Pattern) : d102 (change p 141 (some 163)) = d102 p := by
  change (if p 247 then d12 (change p 141 (some 163)) else d1 (change p 141 (some 163))) = d102 p
  rw [sub3119, sub3192]
  rfl
theorem sub3194 (p : Pattern) : d103 (change p 141 (some 163)) = d103 p := by
  change (if p 246 then d102 (change p 141 (some 163)) else d1 (change p 141 (some 163))) = d103 p
  rw [sub3193, sub3192]
  rfl
theorem sub3195 (p : Pattern) : d104 (change p 141 (some 163)) = d104 p := by
  change (if p 204 then d12 (change p 141 (some 163)) else d103 (change p 141 (some 163))) = d104 p
  rw [sub3119, sub3194]
  rfl
theorem sub3196 (p : Pattern) : d105 (change p 141 (some 163)) = d105 p := by
  change (if p 182 then d104 (change p 141 (some 163)) else d103 (change p 141 (some 163))) = d105 p
  rw [sub3195, sub3194]
  rfl
theorem sub3197 (p : Pattern) : d5 (change p 141 (some 163)) = d5 p := by
  rfl
theorem sub3198 (p : Pattern) : d106 (change p 141 (some 163)) = d106 p := by
  change (if p 247 then d12 (change p 141 (some 163)) else d5 (change p 141 (some 163))) = d106 p
  rw [sub3119, sub3197]
  rfl
theorem sub3199 (p : Pattern) : d107 (change p 141 (some 163)) = d107 p := by
  change (if p 246 then d106 (change p 141 (some 163)) else d5 (change p 141 (some 163))) = d107 p
  rw [sub3198, sub3197]
  rfl
theorem sub3200 (p : Pattern) : d108 (change p 141 (some 163)) = d108 p := by
  change (if p 204 then d12 (change p 141 (some 163)) else d107 (change p 141 (some 163))) = d108 p
  rw [sub3119, sub3199]
  rfl
theorem sub3201 (p : Pattern) : d109 (change p 141 (some 163)) = d109 p := by
  change (if p 182 then d108 (change p 141 (some 163)) else d107 (change p 141 (some 163))) = d109 p
  rw [sub3200, sub3199]
  rfl
theorem sub3202 (p : Pattern) : d110 (change p 141 (some 163)) = d109 p := by
  change d109 (change p 141 (some 163)) = d109 p
  exact sub3201 p
theorem sub3203 (p : Pattern) : d111 (change p 141 (some 163)) = d4168 p := by
  change (if p 162 then d110 (change p 141 (some 163)) else d105 (change p 141 (some 163))) = d4168 p
  rw [sub3202, sub3196]
  rfl
theorem sub3204 (p : Pattern) : d112 (change p 141 (some 163)) = d12 p := by
  change d12 (change p 141 (some 163)) = d12 p
  exact sub3119 p
theorem sub3205 (p : Pattern) : d113 (change p 141 (some 163)) = d1140 p := by
  change (if p 162 then d112 (change p 141 (some 163)) else d110 (change p 141 (some 163))) = d1140 p
  rw [sub3204, sub3202]
  rfl
theorem sub3206 (p : Pattern) : d114 (change p 141 (some 163)) = d4169 p := by
  change (if p 161 then d113 (change p 141 (some 163)) else d111 (change p 141 (some 163))) = d4169 p
  rw [sub3205, sub3203]
  rfl
theorem sub3207 (p : Pattern) : d7 (change p 141 (some 163)) = d7 p := by
  rfl
theorem sub3208 (p : Pattern) : d119 (change p 141 (some 163)) = d119 p := by
  change (if p 247 then d12 (change p 141 (some 163)) else d7 (change p 141 (some 163))) = d119 p
  rw [sub3119, sub3207]
  rfl
theorem sub3209 (p : Pattern) : d120 (change p 141 (some 163)) = d120 p := by
  change (if p 246 then d119 (change p 141 (some 163)) else d7 (change p 141 (some 163))) = d120 p
  rw [sub3208, sub3207]
  rfl
theorem sub3210 (p : Pattern) : d121 (change p 141 (some 163)) = d121 p := by
  change (if p 204 then d12 (change p 141 (some 163)) else d120 (change p 141 (some 163))) = d121 p
  rw [sub3119, sub3209]
  rfl
theorem sub3211 (p : Pattern) : d122 (change p 141 (some 163)) = d122 p := by
  change (if p 182 then d121 (change p 141 (some 163)) else d103 (change p 141 (some 163))) = d122 p
  rw [sub3210, sub3194]
  rfl
theorem sub3212 (p : Pattern) : d123 (change p 141 (some 163)) = d122 p := by
  change d122 (change p 141 (some 163)) = d122 p
  exact sub3211 p
theorem sub3213 (p : Pattern) : d125 (change p 141 (some 163)) = d125 p := by
  change (if p 182 then d12 (change p 141 (some 163)) else d107 (change p 141 (some 163))) = d125 p
  rw [sub3119, sub3199]
  rfl
theorem sub3214 (p : Pattern) : d126 (change p 141 (some 163)) = d125 p := by
  change d125 (change p 141 (some 163)) = d125 p
  exact sub3213 p
theorem sub3215 (p : Pattern) : d127 (change p 141 (some 163)) = d4170 p := by
  change (if p 162 then d126 (change p 141 (some 163)) else d123 (change p 141 (some 163))) = d4170 p
  rw [sub3214, sub3212]
  rfl
theorem sub3216 (p : Pattern) : d128 (change p 141 (some 163)) = d12 p := by
  change d12 (change p 141 (some 163)) = d12 p
  exact sub3119 p
theorem sub3217 (p : Pattern) : d129 (change p 141 (some 163)) = d4171 p := by
  change (if p 162 then d128 (change p 141 (some 163)) else d126 (change p 141 (some 163))) = d4171 p
  rw [sub3216, sub3214]
  rfl
theorem sub3218 (p : Pattern) : d130 (change p 141 (some 163)) = d4172 p := by
  change (if p 161 then d129 (change p 141 (some 163)) else d127 (change p 141 (some 163))) = d4172 p
  rw [sub3217, sub3215]
  rfl
theorem sub3219 (p : Pattern) : d131 (change p 141 (some 163)) = d4173 p := by
  change (if p 160 then d130 (change p 141 (some 163)) else d114 (change p 141 (some 163))) = d4173 p
  rw [sub3218, sub3206]
  rfl
theorem sub3220 (p : Pattern) : d680 (change p 141 (some 163)) = d4173 p := by
  change d131 (change p 141 (some 163)) = d4173 p
  exact sub3219 p
theorem sub3221 (p : Pattern) : d148 (change p 141 (some 163)) = d148 p := by
  change (if p 182 then d121 (change p 141 (some 163)) else d120 (change p 141 (some 163))) = d148 p
  rw [sub3210, sub3209]
  rfl
theorem sub3222 (p : Pattern) : d149 (change p 141 (some 163)) = d148 p := by
  change d148 (change p 141 (some 163)) = d148 p
  exact sub3221 p
theorem sub3223 (p : Pattern) : d150 (change p 141 (some 163)) = d4174 p := by
  change (if p 162 then d12 (change p 141 (some 163)) else d149 (change p 141 (some 163))) = d4174 p
  rw [sub3119, sub3222]
  rfl
theorem sub3224 (p : Pattern) : d151 (change p 141 (some 163)) = d4175 p := by
  change (if p 161 then d12 (change p 141 (some 163)) else d150 (change p 141 (some 163))) = d4175 p
  rw [sub3119, sub3223]
  rfl
theorem sub3225 (p : Pattern) : d152 (change p 141 (some 163)) = d4176 p := by
  change (if p 160 then d151 (change p 141 (some 163)) else d114 (change p 141 (some 163))) = d4176 p
  rw [sub3224, sub3206]
  rfl
theorem sub3226 (p : Pattern) : d681 (change p 141 (some 163)) = d4176 p := by
  change d152 (change p 141 (some 163)) = d4176 p
  exact sub3225 p
theorem sub3227 (p : Pattern) : d682 (change p 141 (some 163)) = d4177 p := by
  change (if p 138 then d681 (change p 141 (some 163)) else d680 (change p 141 (some 163))) = d4177 p
  rw [sub3226, sub3220]
  rfl
theorem sub3228 (p : Pattern) : d683 (change p 141 (some 163)) = d4176 p := by
  change d152 (change p 141 (some 163)) = d4176 p
  exact sub3225 p
theorem sub3229 (p : Pattern) : d159 (change p 141 (some 163)) = d12 p := by
  change (if p 162 then d12 (change p 141 (some 163)) else d112 (change p 141 (some 163))) = d12 p
  rw [sub3119, sub3204]
  simp only [ite_self]
theorem sub3230 (p : Pattern) : d160 (change p 141 (some 163)) = d12 p := by
  change (if p 161 then d12 (change p 141 (some 163)) else d159 (change p 141 (some 163))) = d12 p
  rw [sub3119, sub3229]
  simp only [ite_self]
theorem sub3231 (p : Pattern) : d161 (change p 141 (some 163)) = d12 p := by
  change (if p 160 then d12 (change p 141 (some 163)) else d160 (change p 141 (some 163))) = d12 p
  rw [sub3119, sub3230]
  simp only [ite_self]
theorem sub3232 (p : Pattern) : d162 (change p 141 (some 163)) = d12 p := by
  change d161 (change p 141 (some 163)) = d12 p
  exact sub3231 p
theorem sub3233 (p : Pattern) : d684 (change p 141 (some 163)) = d4178 p := by
  change (if p 138 then d162 (change p 141 (some 163)) else d683 (change p 141 (some 163))) = d4178 p
  rw [sub3232, sub3228]
  rfl
theorem sub3234 (p : Pattern) : d685 (change p 141 (some 163)) = d4179 p := by
  change (if p 116 then d684 (change p 141 (some 163)) else d682 (change p 141 (some 163))) = d4179 p
  rw [sub3233, sub3227]
  rfl
theorem sub3235 (p : Pattern) : d686 (change p 141 (some 163)) = d4173 p := by
  change d131 (change p 141 (some 163)) = d4173 p
  exact sub3219 p
theorem sub3236 (p : Pattern) : d687 (change p 141 (some 163)) = d4176 p := by
  change d152 (change p 141 (some 163)) = d4176 p
  exact sub3225 p
theorem sub3237 (p : Pattern) : d688 (change p 141 (some 163)) = d4177 p := by
  change (if p 138 then d687 (change p 141 (some 163)) else d686 (change p 141 (some 163))) = d4177 p
  rw [sub3236, sub3235]
  rfl
theorem sub3238 (p : Pattern) : d689 (change p 141 (some 163)) = d4176 p := by
  change d152 (change p 141 (some 163)) = d4176 p
  exact sub3225 p
theorem sub3239 (p : Pattern) : d690 (change p 141 (some 163)) = d4178 p := by
  change (if p 138 then d12 (change p 141 (some 163)) else d689 (change p 141 (some 163))) = d4178 p
  rw [sub3119, sub3238]
  rfl
end NetHack.Sokoban22Refined85
