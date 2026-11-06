/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions26
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub3240 (p : Pattern) : d691 (change p 141 (some 163)) = d4179 p := by
  change (if p 116 then d690 (change p 141 (some 163)) else d688 (change p 141 (some 163))) = d4179 p
  rw [sub3239, sub3237]
  rfl
theorem sub3241 (p : Pattern) : d692 (change p 141 (some 163)) = d4179 p := by
  change (if p 115 then d691 (change p 141 (some 163)) else d685 (change p 141 (some 163))) = d4179 p
  rw [sub3240, sub3234]
  simp only [ite_self]
theorem sub3242 (p : Pattern) : d693 (change p 141 (some 163)) = d4180 p := by
  change (if p 71 then d692 (change p 141 (some 163)) else d666 (change p 141 (some 163))) = d4180 p
  rw [sub3241, sub3178]
  rfl
theorem sub3243 (p : Pattern) : d694 (change p 141 (some 163)) = d4181 p := by
  change (if p 49 then d693 (change p 141 (some 163)) else d679 (change p 141 (some 163))) = d4181 p
  rw [sub3242, sub3191]
  rfl
theorem sub3244 (p : Pattern) : d695 (change p 141 (some 163)) = d4173 p := by
  change d131 (change p 141 (some 163)) = d4173 p
  exact sub3219 p
theorem sub3245 (p : Pattern) : d696 (change p 141 (some 163)) = d4176 p := by
  change d152 (change p 141 (some 163)) = d4176 p
  exact sub3225 p
theorem sub3246 (p : Pattern) : d697 (change p 141 (some 163)) = d4177 p := by
  change (if p 138 then d696 (change p 141 (some 163)) else d695 (change p 141 (some 163))) = d4177 p
  rw [sub3245, sub3244]
  rfl
theorem sub3247 (p : Pattern) : d698 (change p 141 (some 163)) = d4176 p := by
  change d152 (change p 141 (some 163)) = d4176 p
  exact sub3225 p
theorem sub3248 (p : Pattern) : d699 (change p 141 (some 163)) = d4178 p := by
  change (if p 138 then d162 (change p 141 (some 163)) else d698 (change p 141 (some 163))) = d4178 p
  rw [sub3232, sub3247]
  rfl
theorem sub3249 (p : Pattern) : d700 (change p 141 (some 163)) = d4179 p := by
  change (if p 116 then d699 (change p 141 (some 163)) else d697 (change p 141 (some 163))) = d4179 p
  rw [sub3248, sub3246]
  rfl
theorem sub3250 (p : Pattern) : d3 (change p 141 (some 163)) = d3 p := by
  rfl
theorem sub3251 (p : Pattern) : d115 (change p 141 (some 163)) = d115 p := by
  change (if p 247 then d12 (change p 141 (some 163)) else d3 (change p 141 (some 163))) = d115 p
  rw [sub3119, sub3250]
  rfl
theorem sub3252 (p : Pattern) : d116 (change p 141 (some 163)) = d116 p := by
  change (if p 246 then d115 (change p 141 (some 163)) else d3 (change p 141 (some 163))) = d116 p
  rw [sub3251, sub3250]
  rfl
theorem sub3253 (p : Pattern) : d268 (change p 141 (some 163)) = d268 p := by
  change (if p 204 then d116 (change p 141 (some 163)) else d103 (change p 141 (some 163))) = d268 p
  rw [sub3252, sub3194]
  rfl
theorem sub3254 (p : Pattern) : d270 (change p 141 (some 163)) = d270 p := by
  change (if p 182 then d121 (change p 141 (some 163)) else d268 (change p 141 (some 163))) = d270 p
  rw [sub3210, sub3253]
  rfl
theorem sub3255 (p : Pattern) : d271 (change p 141 (some 163)) = d270 p := by
  change d270 (change p 141 (some 163)) = d270 p
  exact sub3254 p
theorem sub3256 (p : Pattern) : d273 (change p 141 (some 163)) = d273 p := by
  change (if p 204 then d120 (change p 141 (some 163)) else d107 (change p 141 (some 163))) = d273 p
  rw [sub3209, sub3199]
  rfl
theorem sub3257 (p : Pattern) : d274 (change p 141 (some 163)) = d274 p := by
  change (if p 182 then d12 (change p 141 (some 163)) else d273 (change p 141 (some 163))) = d274 p
  rw [sub3119, sub3256]
  rfl
theorem sub3258 (p : Pattern) : d275 (change p 141 (some 163)) = d274 p := by
  change d274 (change p 141 (some 163)) = d274 p
  exact sub3257 p
theorem sub3259 (p : Pattern) : d276 (change p 141 (some 163)) = d4182 p := by
  change (if p 162 then d275 (change p 141 (some 163)) else d271 (change p 141 (some 163))) = d4182 p
  rw [sub3258, sub3255]
  rfl
theorem sub3260 (p : Pattern) : d278 (change p 141 (some 163)) = d12 p := by
  change d12 (change p 141 (some 163)) = d12 p
  exact sub3119 p
theorem sub3261 (p : Pattern) : d279 (change p 141 (some 163)) = d4183 p := by
  change (if p 162 then d278 (change p 141 (some 163)) else d275 (change p 141 (some 163))) = d4183 p
  rw [sub3260, sub3258]
  rfl
theorem sub3262 (p : Pattern) : d280 (change p 141 (some 163)) = d4184 p := by
  change (if p 161 then d279 (change p 141 (some 163)) else d276 (change p 141 (some 163))) = d4184 p
  rw [sub3261, sub3259]
  rfl
theorem sub3263 (p : Pattern) : d281 (change p 141 (some 163)) = d4185 p := by
  change (if p 160 then d280 (change p 141 (some 163)) else d114 (change p 141 (some 163))) = d4185 p
  rw [sub3262, sub3206]
  rfl
theorem sub3264 (p : Pattern) : d701 (change p 141 (some 163)) = d4185 p := by
  change d281 (change p 141 (some 163)) = d4185 p
  exact sub3263 p
theorem sub3265 (p : Pattern) : d117 (change p 141 (some 163)) = d117 p := by
  change (if p 204 then d12 (change p 141 (some 163)) else d116 (change p 141 (some 163))) = d117 p
  rw [sub3119, sub3252]
  rfl
theorem sub3266 (p : Pattern) : d269 (change p 141 (some 163)) = d269 p := by
  change (if p 182 then d117 (change p 141 (some 163)) else d268 (change p 141 (some 163))) = d269 p
  rw [sub3265, sub3253]
  rfl
theorem sub3267 (p : Pattern) : d291 (change p 141 (some 163)) = d269 p := by
  change d269 (change p 141 (some 163)) = d269 p
  exact sub3266 p
theorem sub3268 (p : Pattern) : d292 (change p 141 (some 163)) = d292 p := by
  change (if p 182 then d121 (change p 141 (some 163)) else d273 (change p 141 (some 163))) = d292 p
  rw [sub3210, sub3256]
  rfl
theorem sub3269 (p : Pattern) : d293 (change p 141 (some 163)) = d292 p := by
  change d292 (change p 141 (some 163)) = d292 p
  exact sub3268 p
theorem sub3270 (p : Pattern) : d294 (change p 141 (some 163)) = d4186 p := by
  change (if p 162 then d293 (change p 141 (some 163)) else d291 (change p 141 (some 163))) = d4186 p
  rw [sub3269, sub3267]
  rfl
theorem sub3271 (p : Pattern) : d295 (change p 141 (some 163)) = d4187 p := by
  change (if p 162 then d278 (change p 141 (some 163)) else d293 (change p 141 (some 163))) = d4187 p
  rw [sub3260, sub3269]
  rfl
theorem sub3272 (p : Pattern) : d296 (change p 141 (some 163)) = d4188 p := by
  change (if p 161 then d295 (change p 141 (some 163)) else d294 (change p 141 (some 163))) = d4188 p
  rw [sub3271, sub3270]
  rfl
theorem sub3273 (p : Pattern) : d297 (change p 141 (some 163)) = d4189 p := by
  change (if p 160 then d151 (change p 141 (some 163)) else d296 (change p 141 (some 163))) = d4189 p
  rw [sub3224, sub3272]
  rfl
theorem sub3274 (p : Pattern) : d702 (change p 141 (some 163)) = d4189 p := by
  change d297 (change p 141 (some 163)) = d4189 p
  exact sub3273 p
theorem sub3275 (p : Pattern) : d703 (change p 141 (some 163)) = d4190 p := by
  change (if p 138 then d702 (change p 141 (some 163)) else d701 (change p 141 (some 163))) = d4190 p
  rw [sub3274, sub3264]
  rfl
theorem sub3276 (p : Pattern) : d704 (change p 141 (some 163)) = d4191 p := by
  change (if p 138 then d12 (change p 141 (some 163)) else d702 (change p 141 (some 163))) = d4191 p
  rw [sub3119, sub3274]
  rfl
theorem sub3277 (p : Pattern) : d705 (change p 141 (some 163)) = d4192 p := by
  change (if p 116 then d704 (change p 141 (some 163)) else d703 (change p 141 (some 163))) = d4192 p
  rw [sub3276, sub3275]
  rfl
theorem sub3278 (p : Pattern) : d706 (change p 141 (some 163)) = d4193 p := by
  change (if p 115 then d705 (change p 141 (some 163)) else d700 (change p 141 (some 163))) = d4193 p
  rw [sub3277, sub3249]
  rfl
theorem sub3279 (p : Pattern) : d707 (change p 141 (some 163)) = d4194 p := by
  change (if p 71 then d706 (change p 141 (some 163)) else d666 (change p 141 (some 163))) = d4194 p
  rw [sub3278, sub3178]
  rfl
theorem sub3280 (p : Pattern) : d708 (change p 141 (some 163)) = d4195 p := by
  change (if p 49 then d707 (change p 141 (some 163)) else d679 (change p 141 (some 163))) = d4195 p
  rw [sub3279, sub3191]
  rfl
theorem sub3281 (p : Pattern) : d709 (change p 141 (some 163)) = d4196 p := by
  change (if p 48 then d708 (change p 141 (some 163)) else d694 (change p 141 (some 163))) = d4196 p
  rw [sub3280, sub3243]
  rfl
theorem sub3282 (p : Pattern) : d0 (change p 116 none) = d0 p := by
  rfl
theorem sub3283 (p : Pattern) : d12 (change p 116 none) = d12 p := by
  rfl
theorem sub3284 (p : Pattern) : d13 (change p 116 none) = d13 p := by
  change (if p 247 then d12 (change p 116 none) else d0 (change p 116 none)) = d13 p
  rw [sub3283, sub3282]
  rfl
theorem sub3285 (p : Pattern) : d14 (change p 116 none) = d14 p := by
  change (if p 246 then d13 (change p 116 none) else d0 (change p 116 none)) = d14 p
  rw [sub3284, sub3282]
  rfl
theorem sub3286 (p : Pattern) : d15 (change p 116 none) = d15 p := by
  change (if p 204 then d12 (change p 116 none) else d14 (change p 116 none)) = d15 p
  rw [sub3283, sub3285]
  rfl
theorem sub3287 (p : Pattern) : d16 (change p 116 none) = d16 p := by
  change (if p 182 then d15 (change p 116 none) else d14 (change p 116 none)) = d16 p
  rw [sub3286, sub3285]
  rfl
theorem sub3288 (p : Pattern) : d4 (change p 116 none) = d4 p := by
  rfl
theorem sub3289 (p : Pattern) : d17 (change p 116 none) = d17 p := by
  change (if p 247 then d12 (change p 116 none) else d4 (change p 116 none)) = d17 p
  rw [sub3283, sub3288]
  rfl
theorem sub3290 (p : Pattern) : d18 (change p 116 none) = d18 p := by
  change (if p 246 then d17 (change p 116 none) else d4 (change p 116 none)) = d18 p
  rw [sub3289, sub3288]
  rfl
theorem sub3291 (p : Pattern) : d19 (change p 116 none) = d19 p := by
  change (if p 204 then d12 (change p 116 none) else d18 (change p 116 none)) = d19 p
  rw [sub3283, sub3290]
  rfl
theorem sub3292 (p : Pattern) : d20 (change p 116 none) = d20 p := by
  change (if p 182 then d19 (change p 116 none) else d18 (change p 116 none)) = d20 p
  rw [sub3291, sub3290]
  rfl
theorem sub3293 (p : Pattern) : d21 (change p 116 none) = d21 p := by
  change (if p 163 then d20 (change p 116 none) else d16 (change p 116 none)) = d21 p
  rw [sub3292, sub3287]
  rfl
theorem sub3294 (p : Pattern) : d22 (change p 116 none) = d22 p := by
  change (if p 162 then d21 (change p 116 none) else d16 (change p 116 none)) = d22 p
  rw [sub3293, sub3287]
  rfl
theorem sub3295 (p : Pattern) : d9 (change p 116 none) = d9 p := by
  rfl
theorem sub3296 (p : Pattern) : d23 (change p 116 none) = d23 p := by
  change (if p 247 then d12 (change p 116 none) else d9 (change p 116 none)) = d23 p
  rw [sub3283, sub3295]
  rfl
theorem sub3297 (p : Pattern) : d24 (change p 116 none) = d24 p := by
  change (if p 246 then d23 (change p 116 none) else d9 (change p 116 none)) = d24 p
  rw [sub3296, sub3295]
  rfl
theorem sub3298 (p : Pattern) : d25 (change p 116 none) = d25 p := by
  change (if p 204 then d12 (change p 116 none) else d24 (change p 116 none)) = d25 p
  rw [sub3283, sub3297]
  rfl
theorem sub3299 (p : Pattern) : d26 (change p 116 none) = d26 p := by
  change (if p 182 then d25 (change p 116 none) else d24 (change p 116 none)) = d26 p
  rw [sub3298, sub3297]
  rfl
theorem sub3300 (p : Pattern) : d27 (change p 116 none) = d27 p := by
  change (if p 163 then d12 (change p 116 none) else d26 (change p 116 none)) = d27 p
  rw [sub3283, sub3299]
  rfl
theorem sub3301 (p : Pattern) : d28 (change p 116 none) = d28 p := by
  change (if p 162 then d27 (change p 116 none) else d21 (change p 116 none)) = d28 p
  rw [sub3300, sub3293]
  rfl
theorem sub3302 (p : Pattern) : d29 (change p 116 none) = d29 p := by
  change (if p 161 then d28 (change p 116 none) else d22 (change p 116 none)) = d29 p
  rw [sub3301, sub3294]
  rfl
theorem sub3303 (p : Pattern) : d2 (change p 116 none) = d2 p := by
  rfl
theorem sub3304 (p : Pattern) : d30 (change p 116 none) = d30 p := by
  change (if p 247 then d12 (change p 116 none) else d2 (change p 116 none)) = d30 p
  rw [sub3283, sub3303]
  rfl
theorem sub3305 (p : Pattern) : d31 (change p 116 none) = d31 p := by
  change (if p 246 then d30 (change p 116 none) else d2 (change p 116 none)) = d31 p
  rw [sub3304, sub3303]
  rfl
theorem sub3306 (p : Pattern) : d32 (change p 116 none) = d32 p := by
  change (if p 204 then d12 (change p 116 none) else d31 (change p 116 none)) = d32 p
  rw [sub3283, sub3305]
  rfl
theorem sub3307 (p : Pattern) : d33 (change p 116 none) = d33 p := by
  change (if p 182 then d32 (change p 116 none) else d14 (change p 116 none)) = d33 p
  rw [sub3306, sub3285]
  rfl
theorem sub3308 (p : Pattern) : d6 (change p 116 none) = d6 p := by
  rfl
theorem sub3309 (p : Pattern) : d34 (change p 116 none) = d34 p := by
  change (if p 247 then d12 (change p 116 none) else d6 (change p 116 none)) = d34 p
  rw [sub3283, sub3308]
  rfl
theorem sub3310 (p : Pattern) : d35 (change p 116 none) = d35 p := by
  change (if p 246 then d34 (change p 116 none) else d6 (change p 116 none)) = d35 p
  rw [sub3309, sub3308]
  rfl
theorem sub3311 (p : Pattern) : d36 (change p 116 none) = d36 p := by
  change (if p 204 then d12 (change p 116 none) else d35 (change p 116 none)) = d36 p
  rw [sub3283, sub3310]
  rfl
theorem sub3312 (p : Pattern) : d37 (change p 116 none) = d37 p := by
  change (if p 182 then d36 (change p 116 none) else d14 (change p 116 none)) = d37 p
  rw [sub3311, sub3285]
  rfl
theorem sub3313 (p : Pattern) : d38 (change p 116 none) = d38 p := by
  change (if p 163 then d37 (change p 116 none) else d33 (change p 116 none)) = d38 p
  rw [sub3312, sub3307]
  rfl
theorem sub3314 (p : Pattern) : d11 (change p 116 none) = d11 p := by
  rfl
theorem sub3315 (p : Pattern) : d39 (change p 116 none) = d39 p := by
  change (if p 247 then d12 (change p 116 none) else d11 (change p 116 none)) = d39 p
  rw [sub3283, sub3314]
  rfl
theorem sub3316 (p : Pattern) : d40 (change p 116 none) = d40 p := by
  change (if p 246 then d39 (change p 116 none) else d11 (change p 116 none)) = d40 p
  rw [sub3315, sub3314]
  rfl
theorem sub3317 (p : Pattern) : d41 (change p 116 none) = d41 p := by
  change (if p 204 then d12 (change p 116 none) else d40 (change p 116 none)) = d41 p
  rw [sub3283, sub3316]
  rfl
theorem sub3318 (p : Pattern) : d42 (change p 116 none) = d42 p := by
  change (if p 182 then d41 (change p 116 none) else d14 (change p 116 none)) = d42 p
  rw [sub3317, sub3285]
  rfl
theorem sub3319 (p : Pattern) : d43 (change p 116 none) = d43 p := by
  change (if p 182 then d12 (change p 116 none) else d18 (change p 116 none)) = d43 p
  rw [sub3283, sub3290]
  rfl
theorem sub3320 (p : Pattern) : d44 (change p 116 none) = d44 p := by
  change (if p 163 then d43 (change p 116 none) else d42 (change p 116 none)) = d44 p
  rw [sub3319, sub3318]
  rfl
theorem sub3321 (p : Pattern) : d45 (change p 116 none) = d45 p := by
  change (if p 162 then d44 (change p 116 none) else d38 (change p 116 none)) = d45 p
  rw [sub3320, sub3313]
  rfl
theorem sub3322 (p : Pattern) : d46 (change p 116 none) = d46 p := by
  change (if p 182 then d12 (change p 116 none) else d14 (change p 116 none)) = d46 p
  rw [sub3283, sub3285]
  rfl
theorem sub3323 (p : Pattern) : d47 (change p 116 none) = d47 p := by
  change (if p 163 then d43 (change p 116 none) else d46 (change p 116 none)) = d47 p
  rw [sub3319, sub3322]
  rfl
theorem sub3324 (p : Pattern) : d48 (change p 116 none) = d48 p := by
  change (if p 182 then d12 (change p 116 none) else d24 (change p 116 none)) = d48 p
  rw [sub3283, sub3297]
  rfl
theorem sub3325 (p : Pattern) : d49 (change p 116 none) = d49 p := by
  change (if p 163 then d12 (change p 116 none) else d48 (change p 116 none)) = d49 p
  rw [sub3283, sub3324]
  rfl
theorem sub3326 (p : Pattern) : d50 (change p 116 none) = d50 p := by
  change (if p 162 then d49 (change p 116 none) else d47 (change p 116 none)) = d50 p
  rw [sub3325, sub3323]
  rfl
theorem sub3327 (p : Pattern) : d51 (change p 116 none) = d51 p := by
  change (if p 161 then d50 (change p 116 none) else d45 (change p 116 none)) = d51 p
  rw [sub3326, sub3321]
  rfl
theorem sub3328 (p : Pattern) : d52 (change p 116 none) = d52 p := by
  change (if p 160 then d51 (change p 116 none) else d29 (change p 116 none)) = d52 p
  rw [sub3327, sub3302]
  rfl
theorem sub3329 (p : Pattern) : d53 (change p 116 none) = d53 p := by
  change (if p 182 then d32 (change p 116 none) else d31 (change p 116 none)) = d53 p
  rw [sub3306, sub3305]
  rfl
theorem sub3330 (p : Pattern) : d54 (change p 116 none) = d54 p := by
  change (if p 163 then d53 (change p 116 none) else d16 (change p 116 none)) = d54 p
  rw [sub3329, sub3287]
  rfl
theorem sub3331 (p : Pattern) : d55 (change p 116 none) = d55 p := by
  change (if p 163 then d26 (change p 116 none) else d20 (change p 116 none)) = d55 p
  rw [sub3299, sub3292]
  rfl
theorem sub3332 (p : Pattern) : d56 (change p 116 none) = d56 p := by
  change (if p 162 then d55 (change p 116 none) else d54 (change p 116 none)) = d56 p
  rw [sub3331, sub3330]
  rfl
theorem sub3333 (p : Pattern) : d10 (change p 116 none) = d10 p := by
  rfl
theorem sub3334 (p : Pattern) : d57 (change p 116 none) = d57 p := by
  change (if p 247 then d12 (change p 116 none) else d10 (change p 116 none)) = d57 p
  rw [sub3283, sub3333]
  rfl
theorem sub3335 (p : Pattern) : d58 (change p 116 none) = d58 p := by
  change (if p 246 then d57 (change p 116 none) else d10 (change p 116 none)) = d58 p
  rw [sub3334, sub3333]
  rfl
theorem sub3336 (p : Pattern) : d59 (change p 116 none) = d59 p := by
  change (if p 204 then d12 (change p 116 none) else d58 (change p 116 none)) = d59 p
  rw [sub3283, sub3335]
  rfl
theorem sub3337 (p : Pattern) : d60 (change p 116 none) = d60 p := by
  change (if p 182 then d59 (change p 116 none) else d58 (change p 116 none)) = d60 p
  rw [sub3336, sub3335]
  rfl
theorem sub3338 (p : Pattern) : d61 (change p 116 none) = d61 p := by
  change (if p 163 then d60 (change p 116 none) else d20 (change p 116 none)) = d61 p
  rw [sub3337, sub3292]
  rfl
theorem sub3339 (p : Pattern) : d62 (change p 116 none) = d62 p := by
  change (if p 182 then d41 (change p 116 none) else d40 (change p 116 none)) = d62 p
  rw [sub3317, sub3316]
  rfl
theorem sub3340 (p : Pattern) : d63 (change p 116 none) = d63 p := by
  change (if p 163 then d12 (change p 116 none) else d62 (change p 116 none)) = d63 p
  rw [sub3283, sub3339]
  rfl
theorem sub3341 (p : Pattern) : d64 (change p 116 none) = d64 p := by
  change (if p 162 then d63 (change p 116 none) else d61 (change p 116 none)) = d64 p
  rw [sub3340, sub3338]
  rfl
theorem sub3342 (p : Pattern) : d65 (change p 116 none) = d65 p := by
  change (if p 161 then d64 (change p 116 none) else d56 (change p 116 none)) = d65 p
  rw [sub3341, sub3332]
  rfl
theorem sub3343 (p : Pattern) : d66 (change p 116 none) = d66 p := by
  change (if p 182 then d12 (change p 116 none) else d31 (change p 116 none)) = d66 p
  rw [sub3283, sub3305]
  rfl
theorem sub3344 (p : Pattern) : d67 (change p 116 none) = d67 p := by
  change (if p 163 then d66 (change p 116 none) else d37 (change p 116 none)) = d67 p
  rw [sub3343, sub3312]
  rfl
theorem sub3345 (p : Pattern) : d68 (change p 116 none) = d68 p := by
  change (if p 163 then d48 (change p 116 none) else d43 (change p 116 none)) = d68 p
  rw [sub3324, sub3319]
  rfl
theorem sub3346 (p : Pattern) : d69 (change p 116 none) = d69 p := by
  change (if p 162 then d68 (change p 116 none) else d67 (change p 116 none)) = d69 p
  rw [sub3345, sub3344]
  rfl
theorem sub3347 (p : Pattern) : d70 (change p 116 none) = d70 p := by
  change (if p 182 then d12 (change p 116 none) else d58 (change p 116 none)) = d70 p
  rw [sub3283, sub3335]
  rfl
theorem sub3348 (p : Pattern) : d71 (change p 116 none) = d71 p := by
  change (if p 163 then d70 (change p 116 none) else d43 (change p 116 none)) = d71 p
  rw [sub3347, sub3319]
  rfl
theorem sub3349 (p : Pattern) : d72 (change p 116 none) = d72 p := by
  change (if p 182 then d12 (change p 116 none) else d40 (change p 116 none)) = d72 p
  rw [sub3283, sub3316]
  rfl
theorem sub3350 (p : Pattern) : d73 (change p 116 none) = d73 p := by
  change (if p 163 then d12 (change p 116 none) else d72 (change p 116 none)) = d73 p
  rw [sub3283, sub3349]
  rfl
theorem sub3351 (p : Pattern) : d74 (change p 116 none) = d74 p := by
  change (if p 162 then d73 (change p 116 none) else d71 (change p 116 none)) = d74 p
  rw [sub3350, sub3348]
  rfl
theorem sub3352 (p : Pattern) : d75 (change p 116 none) = d75 p := by
  change (if p 161 then d74 (change p 116 none) else d69 (change p 116 none)) = d75 p
  rw [sub3351, sub3346]
  rfl
theorem sub3353 (p : Pattern) : d76 (change p 116 none) = d76 p := by
  change (if p 160 then d75 (change p 116 none) else d65 (change p 116 none)) = d76 p
  rw [sub3352, sub3342]
  rfl
theorem sub3354 (p : Pattern) : d77 (change p 116 none) = d77 p := by
  change (if p 141 then d76 (change p 116 none) else d52 (change p 116 none)) = d77 p
  rw [sub3353, sub3328]
  rfl
theorem sub3355 (p : Pattern) : d78 (change p 116 none) = d78 p := by
  change (if p 182 then d36 (change p 116 none) else d35 (change p 116 none)) = d78 p
  rw [sub3311, sub3310]
  rfl
theorem sub3356 (p : Pattern) : d79 (change p 116 none) = d79 p := by
  change (if p 163 then d78 (change p 116 none) else d53 (change p 116 none)) = d79 p
  rw [sub3355, sub3329]
  rfl
theorem sub3357 (p : Pattern) : d80 (change p 116 none) = d80 p := by
  change (if p 162 then d63 (change p 116 none) else d79 (change p 116 none)) = d80 p
  rw [sub3340, sub3356]
  rfl
theorem sub3358 (p : Pattern) : d81 (change p 116 none) = d81 p := by
  change (if p 161 then d12 (change p 116 none) else d80 (change p 116 none)) = d81 p
  rw [sub3283, sub3357]
  rfl
theorem sub3359 (p : Pattern) : d82 (change p 116 none) = d82 p := by
  change (if p 160 then d81 (change p 116 none) else d29 (change p 116 none)) = d82 p
  rw [sub3358, sub3302]
  rfl
end NetHack.Sokoban22Refined85
