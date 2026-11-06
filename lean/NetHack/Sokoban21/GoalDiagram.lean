/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Range
namespace NetHack.Sokoban21.Diagram
def d3241 (pattern : Twelve) : Int := if pattern.k then d1866 pattern else d1 pattern
theorem range3241 (pattern : Twelve) : 0 ≤ d3241 pattern ∧ d3241 pattern ≤ 6 := by
  unfold d3241
  split
  · exact range1866 pattern
  · exact range1 pattern
def d3242 (pattern : Twelve) : Int := if pattern.i then d3241 pattern else d1 pattern
theorem range3242 (pattern : Twelve) : 0 ≤ d3242 pattern ∧ d3242 pattern ≤ 6 := by
  unfold d3242
  split
  · exact range3241 pattern
  · exact range1 pattern
def d3243 (pattern : Twelve) : Int := if pattern.h then d3242 pattern else d1 pattern
theorem range3243 (pattern : Twelve) : 0 ≤ d3243 pattern ∧ d3243 pattern ≤ 6 := by
  unfold d3243
  split
  · exact range3242 pattern
  · exact range1 pattern
def d3244 (pattern : Twelve) : Int := if pattern.i then d1867 pattern else d3241 pattern
theorem range3244 (pattern : Twelve) : 0 ≤ d3244 pattern ∧ d3244 pattern ≤ 6 := by
  unfold d3244
  split
  · exact range1867 pattern
  · exact range3241 pattern
def d3245 (pattern : Twelve) : Int := if pattern.h then d3244 pattern else d3242 pattern
theorem range3245 (pattern : Twelve) : 0 ≤ d3245 pattern ∧ d3245 pattern ≤ 6 := by
  unfold d3245
  split
  · exact range3244 pattern
  · exact range3242 pattern
def d3246 (pattern : Twelve) : Int := if pattern.f then d3245 pattern else d3243 pattern
theorem range3246 (pattern : Twelve) : 0 ≤ d3246 pattern ∧ d3246 pattern ≤ 6 := by
  unfold d3246
  split
  · exact range3245 pattern
  · exact range3243 pattern
def d3247 (pattern : Twelve) : Int := if pattern.i then d0 pattern else d1867 pattern
theorem range3247 (pattern : Twelve) : 0 ≤ d3247 pattern ∧ d3247 pattern ≤ 6 := by
  unfold d3247
  split
  · exact range0 pattern
  · exact range1867 pattern
def d3248 (pattern : Twelve) : Int := if pattern.h then d3247 pattern else d3244 pattern
theorem range3248 (pattern : Twelve) : 0 ≤ d3248 pattern ∧ d3248 pattern ≤ 6 := by
  unfold d3248
  split
  · exact range3247 pattern
  · exact range3244 pattern
def d3249 (pattern : Twelve) : Int := if pattern.f then d3248 pattern else d3245 pattern
theorem range3249 (pattern : Twelve) : 0 ≤ d3249 pattern ∧ d3249 pattern ≤ 6 := by
  unfold d3249
  split
  · exact range3248 pattern
  · exact range3245 pattern
def d3250 (pattern : Twelve) : Int := if pattern.e then d3249 pattern else d3246 pattern
theorem range3250 (pattern : Twelve) : 0 ≤ d3250 pattern ∧ d3250 pattern ≤ 6 := by
  unfold d3250
  split
  · exact range3249 pattern
  · exact range3246 pattern
def d3251 (pattern : Twelve) : Int := if pattern.h then d0 pattern else d3247 pattern
theorem range3251 (pattern : Twelve) : 0 ≤ d3251 pattern ∧ d3251 pattern ≤ 6 := by
  unfold d3251
  split
  · exact range0 pattern
  · exact range3247 pattern
def d3252 (pattern : Twelve) : Int := if pattern.f then d3251 pattern else d3248 pattern
theorem range3252 (pattern : Twelve) : 0 ≤ d3252 pattern ∧ d3252 pattern ≤ 6 := by
  unfold d3252
  split
  · exact range3251 pattern
  · exact range3248 pattern
def d3253 (pattern : Twelve) : Int := if pattern.e then d3252 pattern else d3249 pattern
theorem range3253 (pattern : Twelve) : 0 ≤ d3253 pattern ∧ d3253 pattern ≤ 6 := by
  unfold d3253
  split
  · exact range3252 pattern
  · exact range3249 pattern
def d3254 (pattern : Twelve) : Int := if pattern.j then d3253 pattern else d3250 pattern
theorem range3254 (pattern : Twelve) : 0 ≤ d3254 pattern ∧ d3254 pattern ≤ 6 := by
  unfold d3254
  split
  · exact range3253 pattern
  · exact range3250 pattern
def d3255 (pattern : Twelve) : Int := if pattern.f then d0 pattern else d3251 pattern
theorem range3255 (pattern : Twelve) : 0 ≤ d3255 pattern ∧ d3255 pattern ≤ 6 := by
  unfold d3255
  split
  · exact range0 pattern
  · exact range3251 pattern
def d3256 (pattern : Twelve) : Int := if pattern.e then d3255 pattern else d3252 pattern
theorem range3256 (pattern : Twelve) : 0 ≤ d3256 pattern ∧ d3256 pattern ≤ 6 := by
  unfold d3256
  split
  · exact range3255 pattern
  · exact range3252 pattern
def d3257 (pattern : Twelve) : Int := if pattern.j then d3256 pattern else d3253 pattern
theorem range3257 (pattern : Twelve) : 0 ≤ d3257 pattern ∧ d3257 pattern ≤ 6 := by
  unfold d3257
  split
  · exact range3256 pattern
  · exact range3253 pattern
def d3258 (pattern : Twelve) : Int := if pattern.d then d3257 pattern else d3254 pattern
theorem range3258 (pattern : Twelve) : 0 ≤ d3258 pattern ∧ d3258 pattern ≤ 6 := by
  unfold d3258
  split
  · exact range3257 pattern
  · exact range3254 pattern
def d3259 (pattern : Twelve) : Int := if pattern.e then d0 pattern else d3255 pattern
theorem range3259 (pattern : Twelve) : 0 ≤ d3259 pattern ∧ d3259 pattern ≤ 6 := by
  unfold d3259
  split
  · exact range0 pattern
  · exact range3255 pattern
def d3260 (pattern : Twelve) : Int := if pattern.j then d3259 pattern else d3256 pattern
theorem range3260 (pattern : Twelve) : 0 ≤ d3260 pattern ∧ d3260 pattern ≤ 6 := by
  unfold d3260
  split
  · exact range3259 pattern
  · exact range3256 pattern
def d3261 (pattern : Twelve) : Int := if pattern.d then d3260 pattern else d3257 pattern
theorem range3261 (pattern : Twelve) : 0 ≤ d3261 pattern ∧ d3261 pattern ≤ 6 := by
  unfold d3261
  split
  · exact range3260 pattern
  · exact range3257 pattern
def d3262 (pattern : Twelve) : Int := if pattern.c then d3261 pattern else d3258 pattern
theorem range3262 (pattern : Twelve) : 0 ≤ d3262 pattern ∧ d3262 pattern ≤ 6 := by
  unfold d3262
  split
  · exact range3261 pattern
  · exact range3258 pattern
def d3263 (pattern : Twelve) : Int := if pattern.j then d0 pattern else d3259 pattern
theorem range3263 (pattern : Twelve) : 0 ≤ d3263 pattern ∧ d3263 pattern ≤ 6 := by
  unfold d3263
  split
  · exact range0 pattern
  · exact range3259 pattern
def d3264 (pattern : Twelve) : Int := if pattern.d then d3263 pattern else d3260 pattern
theorem range3264 (pattern : Twelve) : 0 ≤ d3264 pattern ∧ d3264 pattern ≤ 6 := by
  unfold d3264
  split
  · exact range3263 pattern
  · exact range3260 pattern
def d3265 (pattern : Twelve) : Int := if pattern.c then d3264 pattern else d3261 pattern
theorem range3265 (pattern : Twelve) : 0 ≤ d3265 pattern ∧ d3265 pattern ≤ 6 := by
  unfold d3265
  split
  · exact range3264 pattern
  · exact range3261 pattern
def d3266 (pattern : Twelve) : Int := if pattern.g then d3265 pattern else d3262 pattern
theorem range3266 (pattern : Twelve) : 0 ≤ d3266 pattern ∧ d3266 pattern ≤ 6 := by
  unfold d3266
  split
  · exact range3265 pattern
  · exact range3262 pattern
def d3267 (pattern : Twelve) : Int := if pattern.d then d0 pattern else d3263 pattern
theorem range3267 (pattern : Twelve) : 0 ≤ d3267 pattern ∧ d3267 pattern ≤ 6 := by
  unfold d3267
  split
  · exact range0 pattern
  · exact range3263 pattern
def d3268 (pattern : Twelve) : Int := if pattern.c then d3267 pattern else d3264 pattern
theorem range3268 (pattern : Twelve) : 0 ≤ d3268 pattern ∧ d3268 pattern ≤ 6 := by
  unfold d3268
  split
  · exact range3267 pattern
  · exact range3264 pattern
def d3269 (pattern : Twelve) : Int := if pattern.g then d3268 pattern else d3265 pattern
theorem range3269 (pattern : Twelve) : 0 ≤ d3269 pattern ∧ d3269 pattern ≤ 6 := by
  unfold d3269
  split
  · exact range3268 pattern
  · exact range3265 pattern
def d3270 (pattern : Twelve) : Int := if pattern.b then d3269 pattern else d3266 pattern
theorem range3270 (pattern : Twelve) : 0 ≤ d3270 pattern ∧ d3270 pattern ≤ 6 := by
  unfold d3270
  split
  · exact range3269 pattern
  · exact range3266 pattern
def d3271 (pattern : Twelve) : Int := if pattern.c then d0 pattern else d3267 pattern
theorem range3271 (pattern : Twelve) : 0 ≤ d3271 pattern ∧ d3271 pattern ≤ 6 := by
  unfold d3271
  split
  · exact range0 pattern
  · exact range3267 pattern
def d3272 (pattern : Twelve) : Int := if pattern.g then d3271 pattern else d3268 pattern
theorem range3272 (pattern : Twelve) : 0 ≤ d3272 pattern ∧ d3272 pattern ≤ 6 := by
  unfold d3272
  split
  · exact range3271 pattern
  · exact range3268 pattern
def d3273 (pattern : Twelve) : Int := if pattern.b then d3272 pattern else d3269 pattern
theorem range3273 (pattern : Twelve) : 0 ≤ d3273 pattern ∧ d3273 pattern ≤ 6 := by
  unfold d3273
  split
  · exact range3272 pattern
  · exact range3269 pattern
def d3274 (pattern : Twelve) : Int := if pattern.a then d3273 pattern else d3270 pattern
theorem range3274 (pattern : Twelve) : 0 ≤ d3274 pattern ∧ d3274 pattern ≤ 6 := by
  unfold d3274
  split
  · exact range3273 pattern
  · exact range3270 pattern
def d3275 (pattern : Twelve) : Int := if pattern.g then d0 pattern else d3271 pattern
theorem range3275 (pattern : Twelve) : 0 ≤ d3275 pattern ∧ d3275 pattern ≤ 6 := by
  unfold d3275
  split
  · exact range0 pattern
  · exact range3271 pattern
def d3276 (pattern : Twelve) : Int := if pattern.b then d3275 pattern else d3272 pattern
theorem range3276 (pattern : Twelve) : 0 ≤ d3276 pattern ∧ d3276 pattern ≤ 6 := by
  unfold d3276
  split
  · exact range3275 pattern
  · exact range3272 pattern
def d3277 (pattern : Twelve) : Int := if pattern.a then d3276 pattern else d3273 pattern
theorem range3277 (pattern : Twelve) : 0 ≤ d3277 pattern ∧ d3277 pattern ≤ 6 := by
  unfold d3277
  split
  · exact range3276 pattern
  · exact range3273 pattern
def d3278 (pattern : Twelve) : Int := if pattern.b then d0 pattern else d3275 pattern
theorem range3278 (pattern : Twelve) : 0 ≤ d3278 pattern ∧ d3278 pattern ≤ 6 := by
  unfold d3278
  split
  · exact range0 pattern
  · exact range3275 pattern
def d3279 (pattern : Twelve) : Int := if pattern.a then d3278 pattern else d3276 pattern
theorem range3279 (pattern : Twelve) : 0 ≤ d3279 pattern ∧ d3279 pattern ≤ 6 := by
  unfold d3279
  split
  · exact range3278 pattern
  · exact range3276 pattern
def d3280 (pattern : Twelve) : Int := if pattern.a then d0 pattern else d3278 pattern
theorem range3280 (pattern : Twelve) : 0 ≤ d3280 pattern ∧ d3280 pattern ≤ 6 := by
  unfold d3280
  split
  · exact range0 pattern
  · exact range3278 pattern
def d3281 (pattern : Twelve) : Int := if pattern.j then d778 pattern else d26 pattern
theorem range3281 (pattern : Twelve) : 0 ≤ d3281 pattern ∧ d3281 pattern ≤ 6 := by
  unfold d3281
  split
  · exact range778 pattern
  · exact range26 pattern
def d3282 (pattern : Twelve) : Int := if pattern.i then d5 pattern else d4 pattern
theorem range3282 (pattern : Twelve) : 0 ≤ d3282 pattern ∧ d3282 pattern ≤ 6 := by
  unfold d3282
  split
  · exact range5 pattern
  · exact range4 pattern
def d3283 (pattern : Twelve) : Int := if pattern.j then d3282 pattern else d778 pattern
theorem range3283 (pattern : Twelve) : 0 ≤ d3283 pattern ∧ d3283 pattern ≤ 6 := by
  unfold d3283
  split
  · exact range3282 pattern
  · exact range778 pattern
def d3284 (pattern : Twelve) : Int := if pattern.d then d3283 pattern else d3281 pattern
theorem range3284 (pattern : Twelve) : 0 ≤ d3284 pattern ∧ d3284 pattern ≤ 6 := by
  unfold d3284
  split
  · exact range3283 pattern
  · exact range3281 pattern
def d3285 (pattern : Twelve) : Int := if pattern.i then d4 pattern else d3 pattern
theorem range3285 (pattern : Twelve) : 0 ≤ d3285 pattern ∧ d3285 pattern ≤ 6 := by
  unfold d3285
  split
  · exact range4 pattern
  · exact range3 pattern
def d3286 (pattern : Twelve) : Int := if pattern.j then d781 pattern else d3285 pattern
theorem range3286 (pattern : Twelve) : 0 ≤ d3286 pattern ∧ d3286 pattern ≤ 6 := by
  unfold d3286
  split
  · exact range781 pattern
  · exact range3285 pattern
def d3287 (pattern : Twelve) : Int := if pattern.j then d6 pattern else d781 pattern
theorem range3287 (pattern : Twelve) : 0 ≤ d3287 pattern ∧ d3287 pattern ≤ 6 := by
  unfold d3287
  split
  · exact range6 pattern
  · exact range781 pattern
def d3288 (pattern : Twelve) : Int := if pattern.d then d3287 pattern else d3286 pattern
theorem range3288 (pattern : Twelve) : 0 ≤ d3288 pattern ∧ d3288 pattern ≤ 6 := by
  unfold d3288
  split
  · exact range3287 pattern
  · exact range3286 pattern
def d3289 (pattern : Twelve) : Int := if pattern.c then d3288 pattern else d3284 pattern
theorem range3289 (pattern : Twelve) : 0 ≤ d3289 pattern ∧ d3289 pattern ≤ 6 := by
  unfold d3289
  split
  · exact range3288 pattern
  · exact range3284 pattern
def d3290 (pattern : Twelve) : Int := if pattern.g then d6 pattern else d3289 pattern
theorem range3290 (pattern : Twelve) : 0 ≤ d3290 pattern ∧ d3290 pattern ≤ 6 := by
  unfold d3290
  split
  · exact range6 pattern
  · exact range3289 pattern
def d3291 (pattern : Twelve) : Int := if pattern.b then d6 pattern else d3290 pattern
theorem range3291 (pattern : Twelve) : 0 ≤ d3291 pattern ∧ d3291 pattern ≤ 6 := by
  unfold d3291
  split
  · exact range6 pattern
  · exact range3290 pattern
def d3292 (pattern : Twelve) : Int := if pattern.a then d6 pattern else d3291 pattern
theorem range3292 (pattern : Twelve) : 0 ≤ d3292 pattern ∧ d3292 pattern ≤ 6 := by
  unfold d3292
  split
  · exact range6 pattern
  · exact range3291 pattern
end NetHack.Sokoban21.Diagram
