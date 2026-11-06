/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes26
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d3240 (p : Pattern) : Int := if p 204 then d12 p else d3239 p
theorem agree3240 (p q : Pattern) (h : Agree support p q) : d3240 p = d3240 q := by
  simp only [d3240, h 204 (by decide), agree12 p q h, agree3239 p q h]
theorem nonnegative3240 (p : Pattern) : 0 ≤ d3240 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3239 p)
def d3241 (p : Pattern) : Int := if p 182 then d3240 p else d3239 p
theorem agree3241 (p q : Pattern) (h : Agree support p q) : d3241 p = d3241 q := by
  simp only [d3241, h 182 (by decide), agree3240 p q h, agree3239 p q h]
theorem nonnegative3241 (p : Pattern) : 0 ≤ d3241 p :=
  nonnegative_ite (p 182) (nonnegative3240 p) (nonnegative3239 p)
def d3242 (p : Pattern) : Int := if p 163 then d3241 p else d3238 p
theorem agree3242 (p q : Pattern) (h : Agree support p q) : d3242 p = d3242 q := by
  simp only [d3242, h 163 (by decide), agree3241 p q h, agree3238 p q h]
theorem nonnegative3242 (p : Pattern) : 0 ≤ d3242 p :=
  nonnegative_ite (p 163) (nonnegative3241 p) (nonnegative3238 p)
def d3243 (p : Pattern) : Int := if p 162 then d3242 p else d3237 p
theorem agree3243 (p q : Pattern) (h : Agree support p q) : d3243 p = d3243 q := by
  simp only [d3243, h 162 (by decide), agree3242 p q h, agree3237 p q h]
theorem nonnegative3243 (p : Pattern) : 0 ≤ d3243 p :=
  nonnegative_ite (p 162) (nonnegative3242 p) (nonnegative3237 p)
def d3244 (p : Pattern) : Int := if p 246 then d12 p else d9 p
theorem agree3244 (p q : Pattern) (h : Agree support p q) : d3244 p = d3244 q := by
  simp only [d3244, h 246 (by decide), agree12 p q h, agree9 p q h]
theorem nonnegative3244 (p : Pattern) : 0 ≤ d3244 p :=
  nonnegative_ite (p 246) (nonnegative12 p) (nonnegative9 p)
def d3245 (p : Pattern) : Int := if p 204 then d12 p else d3244 p
theorem agree3245 (p q : Pattern) (h : Agree support p q) : d3245 p = d3245 q := by
  simp only [d3245, h 204 (by decide), agree12 p q h, agree3244 p q h]
theorem nonnegative3245 (p : Pattern) : 0 ≤ d3245 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3244 p)
def d3246 (p : Pattern) : Int := if p 182 then d3245 p else d3244 p
theorem agree3246 (p q : Pattern) (h : Agree support p q) : d3246 p = d3246 q := by
  simp only [d3246, h 182 (by decide), agree3245 p q h, agree3244 p q h]
theorem nonnegative3246 (p : Pattern) : 0 ≤ d3246 p :=
  nonnegative_ite (p 182) (nonnegative3245 p) (nonnegative3244 p)
def d3247 (p : Pattern) : Int := if p 163 then d12 p else d3246 p
theorem agree3247 (p q : Pattern) (h : Agree support p q) : d3247 p = d3247 q := by
  simp only [d3247, h 163 (by decide), agree12 p q h, agree3246 p q h]
theorem nonnegative3247 (p : Pattern) : 0 ≤ d3247 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3246 p)
def d3248 (p : Pattern) : Int := if p 162 then d3247 p else d3242 p
theorem agree3248 (p q : Pattern) (h : Agree support p q) : d3248 p = d3248 q := by
  simp only [d3248, h 162 (by decide), agree3247 p q h, agree3242 p q h]
theorem nonnegative3248 (p : Pattern) : 0 ≤ d3248 p :=
  nonnegative_ite (p 162) (nonnegative3247 p) (nonnegative3242 p)
def d3249 (p : Pattern) : Int := if p 161 then d3248 p else d3243 p
theorem agree3249 (p q : Pattern) (h : Agree support p q) : d3249 p = d3249 q := by
  simp only [d3249, h 161 (by decide), agree3248 p q h, agree3243 p q h]
theorem nonnegative3249 (p : Pattern) : 0 ≤ d3249 p :=
  nonnegative_ite (p 161) (nonnegative3248 p) (nonnegative3243 p)
def d3250 (p : Pattern) : Int := if p 246 then d12 p else d2 p
theorem agree3250 (p q : Pattern) (h : Agree support p q) : d3250 p = d3250 q := by
  simp only [d3250, h 246 (by decide), agree12 p q h, agree2 p q h]
theorem nonnegative3250 (p : Pattern) : 0 ≤ d3250 p :=
  nonnegative_ite (p 246) (nonnegative12 p) (nonnegative2 p)
def d3251 (p : Pattern) : Int := if p 204 then d12 p else d3250 p
theorem agree3251 (p q : Pattern) (h : Agree support p q) : d3251 p = d3251 q := by
  simp only [d3251, h 204 (by decide), agree12 p q h, agree3250 p q h]
theorem nonnegative3251 (p : Pattern) : 0 ≤ d3251 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3250 p)
def d3252 (p : Pattern) : Int := if p 182 then d3251 p else d3226 p
theorem agree3252 (p q : Pattern) (h : Agree support p q) : d3252 p = d3252 q := by
  simp only [d3252, h 182 (by decide), agree3251 p q h, agree3226 p q h]
theorem nonnegative3252 (p : Pattern) : 0 ≤ d3252 p :=
  nonnegative_ite (p 182) (nonnegative3251 p) (nonnegative3226 p)
def d3253 (p : Pattern) : Int := if p 246 then d12 p else d6 p
theorem agree3253 (p q : Pattern) (h : Agree support p q) : d3253 p = d3253 q := by
  simp only [d3253, h 246 (by decide), agree12 p q h, agree6 p q h]
theorem nonnegative3253 (p : Pattern) : 0 ≤ d3253 p :=
  nonnegative_ite (p 246) (nonnegative12 p) (nonnegative6 p)
def d3254 (p : Pattern) : Int := if p 204 then d12 p else d3253 p
theorem agree3254 (p q : Pattern) (h : Agree support p q) : d3254 p = d3254 q := by
  simp only [d3254, h 204 (by decide), agree12 p q h, agree3253 p q h]
theorem nonnegative3254 (p : Pattern) : 0 ≤ d3254 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3253 p)
def d3255 (p : Pattern) : Int := if p 182 then d3254 p else d3226 p
theorem agree3255 (p q : Pattern) (h : Agree support p q) : d3255 p = d3255 q := by
  simp only [d3255, h 182 (by decide), agree3254 p q h, agree3226 p q h]
theorem nonnegative3255 (p : Pattern) : 0 ≤ d3255 p :=
  nonnegative_ite (p 182) (nonnegative3254 p) (nonnegative3226 p)
def d3256 (p : Pattern) : Int := if p 163 then d3255 p else d3252 p
theorem agree3256 (p q : Pattern) (h : Agree support p q) : d3256 p = d3256 q := by
  simp only [d3256, h 163 (by decide), agree3255 p q h, agree3252 p q h]
theorem nonnegative3256 (p : Pattern) : 0 ≤ d3256 p :=
  nonnegative_ite (p 163) (nonnegative3255 p) (nonnegative3252 p)
def d3257 (p : Pattern) : Int := if p 246 then d12 p else d11 p
theorem agree3257 (p q : Pattern) (h : Agree support p q) : d3257 p = d3257 q := by
  simp only [d3257, h 246 (by decide), agree12 p q h, agree11 p q h]
theorem nonnegative3257 (p : Pattern) : 0 ≤ d3257 p :=
  nonnegative_ite (p 246) (nonnegative12 p) (nonnegative11 p)
def d3258 (p : Pattern) : Int := if p 204 then d12 p else d3257 p
theorem agree3258 (p q : Pattern) (h : Agree support p q) : d3258 p = d3258 q := by
  simp only [d3258, h 204 (by decide), agree12 p q h, agree3257 p q h]
theorem nonnegative3258 (p : Pattern) : 0 ≤ d3258 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3257 p)
def d3259 (p : Pattern) : Int := if p 182 then d3258 p else d3226 p
theorem agree3259 (p q : Pattern) (h : Agree support p q) : d3259 p = d3259 q := by
  simp only [d3259, h 182 (by decide), agree3258 p q h, agree3226 p q h]
theorem nonnegative3259 (p : Pattern) : 0 ≤ d3259 p :=
  nonnegative_ite (p 182) (nonnegative3258 p) (nonnegative3226 p)
def d3260 (p : Pattern) : Int := if p 182 then d12 p else d3239 p
theorem agree3260 (p q : Pattern) (h : Agree support p q) : d3260 p = d3260 q := by
  simp only [d3260, h 182 (by decide), agree12 p q h, agree3239 p q h]
theorem nonnegative3260 (p : Pattern) : 0 ≤ d3260 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3239 p)
def d3261 (p : Pattern) : Int := if p 163 then d3260 p else d3259 p
theorem agree3261 (p q : Pattern) (h : Agree support p q) : d3261 p = d3261 q := by
  simp only [d3261, h 163 (by decide), agree3260 p q h, agree3259 p q h]
theorem nonnegative3261 (p : Pattern) : 0 ≤ d3261 p :=
  nonnegative_ite (p 163) (nonnegative3260 p) (nonnegative3259 p)
def d3262 (p : Pattern) : Int := if p 162 then d3261 p else d3256 p
theorem agree3262 (p q : Pattern) (h : Agree support p q) : d3262 p = d3262 q := by
  simp only [d3262, h 162 (by decide), agree3261 p q h, agree3256 p q h]
theorem nonnegative3262 (p : Pattern) : 0 ≤ d3262 p :=
  nonnegative_ite (p 162) (nonnegative3261 p) (nonnegative3256 p)
def d3263 (p : Pattern) : Int := if p 182 then d12 p else d3226 p
theorem agree3263 (p q : Pattern) (h : Agree support p q) : d3263 p = d3263 q := by
  simp only [d3263, h 182 (by decide), agree12 p q h, agree3226 p q h]
theorem nonnegative3263 (p : Pattern) : 0 ≤ d3263 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3226 p)
def d3264 (p : Pattern) : Int := if p 163 then d3260 p else d3263 p
theorem agree3264 (p q : Pattern) (h : Agree support p q) : d3264 p = d3264 q := by
  simp only [d3264, h 163 (by decide), agree3260 p q h, agree3263 p q h]
theorem nonnegative3264 (p : Pattern) : 0 ≤ d3264 p :=
  nonnegative_ite (p 163) (nonnegative3260 p) (nonnegative3263 p)
def d3265 (p : Pattern) : Int := if p 182 then d12 p else d3244 p
theorem agree3265 (p q : Pattern) (h : Agree support p q) : d3265 p = d3265 q := by
  simp only [d3265, h 182 (by decide), agree12 p q h, agree3244 p q h]
theorem nonnegative3265 (p : Pattern) : 0 ≤ d3265 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3244 p)
def d3266 (p : Pattern) : Int := if p 163 then d12 p else d3265 p
theorem agree3266 (p q : Pattern) (h : Agree support p q) : d3266 p = d3266 q := by
  simp only [d3266, h 163 (by decide), agree12 p q h, agree3265 p q h]
theorem nonnegative3266 (p : Pattern) : 0 ≤ d3266 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3265 p)
def d3267 (p : Pattern) : Int := if p 162 then d3266 p else d3264 p
theorem agree3267 (p q : Pattern) (h : Agree support p q) : d3267 p = d3267 q := by
  simp only [d3267, h 162 (by decide), agree3266 p q h, agree3264 p q h]
theorem nonnegative3267 (p : Pattern) : 0 ≤ d3267 p :=
  nonnegative_ite (p 162) (nonnegative3266 p) (nonnegative3264 p)
def d3268 (p : Pattern) : Int := if p 161 then d3267 p else d3262 p
theorem agree3268 (p q : Pattern) (h : Agree support p q) : d3268 p = d3268 q := by
  simp only [d3268, h 161 (by decide), agree3267 p q h, agree3262 p q h]
theorem nonnegative3268 (p : Pattern) : 0 ≤ d3268 p :=
  nonnegative_ite (p 161) (nonnegative3267 p) (nonnegative3262 p)
def d3269 (p : Pattern) : Int := if p 160 then d3268 p else d3249 p
theorem agree3269 (p q : Pattern) (h : Agree support p q) : d3269 p = d3269 q := by
  simp only [d3269, h 160 (by decide), agree3268 p q h, agree3249 p q h]
theorem nonnegative3269 (p : Pattern) : 0 ≤ d3269 p :=
  nonnegative_ite (p 160) (nonnegative3268 p) (nonnegative3249 p)
def d3270 (p : Pattern) : Int := if p 246 then d57 p else d0 p
theorem agree3270 (p q : Pattern) (h : Agree support p q) : d3270 p = d3270 q := by
  simp only [d3270, h 246 (by decide), agree57 p q h, agree0 p q h]
theorem nonnegative3270 (p : Pattern) : 0 ≤ d3270 p :=
  nonnegative_ite (p 246) (nonnegative57 p) (nonnegative0 p)
def d3271 (p : Pattern) : Int := if p 225 then d3226 p else d3270 p
theorem agree3271 (p q : Pattern) (h : Agree support p q) : d3271 p = d3271 q := by
  simp only [d3271, h 225 (by decide), agree3226 p q h, agree3270 p q h]
theorem nonnegative3271 (p : Pattern) : 0 ≤ d3271 p :=
  nonnegative_ite (p 225) (nonnegative3226 p) (nonnegative3270 p)
def d3272 (p : Pattern) : Int := if p 224 then d3226 p else d3271 p
theorem agree3272 (p q : Pattern) (h : Agree support p q) : d3272 p = d3272 q := by
  simp only [d3272, h 224 (by decide), agree3226 p q h, agree3271 p q h]
theorem nonnegative3272 (p : Pattern) : 0 ≤ d3272 p :=
  nonnegative_ite (p 224) (nonnegative3226 p) (nonnegative3271 p)
def d3273 (p : Pattern) : Int := if p 204 then d3226 p else d3272 p
theorem agree3273 (p q : Pattern) (h : Agree support p q) : d3273 p = d3273 q := by
  simp only [d3273, h 204 (by decide), agree3226 p q h, agree3272 p q h]
theorem nonnegative3273 (p : Pattern) : 0 ≤ d3273 p :=
  nonnegative_ite (p 204) (nonnegative3226 p) (nonnegative3272 p)
def d3274 (p : Pattern) : Int := if p 182 then d3230 p else d3273 p
theorem agree3274 (p q : Pattern) (h : Agree support p q) : d3274 p = d3274 q := by
  simp only [d3274, h 182 (by decide), agree3230 p q h, agree3273 p q h]
theorem nonnegative3274 (p : Pattern) : 0 ≤ d3274 p :=
  nonnegative_ite (p 182) (nonnegative3230 p) (nonnegative3273 p)
def d3275 (p : Pattern) : Int := if p 182 then d3251 p else d3250 p
theorem agree3275 (p q : Pattern) (h : Agree support p q) : d3275 p = d3275 q := by
  simp only [d3275, h 182 (by decide), agree3251 p q h, agree3250 p q h]
theorem nonnegative3275 (p : Pattern) : 0 ≤ d3275 p :=
  nonnegative_ite (p 182) (nonnegative3251 p) (nonnegative3250 p)
def d3276 (p : Pattern) : Int := if p 163 then d3275 p else d3274 p
theorem agree3276 (p q : Pattern) (h : Agree support p q) : d3276 p = d3276 q := by
  simp only [d3276, h 163 (by decide), agree3275 p q h, agree3274 p q h]
theorem nonnegative3276 (p : Pattern) : 0 ≤ d3276 p :=
  nonnegative_ite (p 163) (nonnegative3275 p) (nonnegative3274 p)
def d3277 (p : Pattern) : Int := if p 163 then d3246 p else d3241 p
theorem agree3277 (p q : Pattern) (h : Agree support p q) : d3277 p = d3277 q := by
  simp only [d3277, h 163 (by decide), agree3246 p q h, agree3241 p q h]
theorem nonnegative3277 (p : Pattern) : 0 ≤ d3277 p :=
  nonnegative_ite (p 163) (nonnegative3246 p) (nonnegative3241 p)
def d3278 (p : Pattern) : Int := if p 162 then d3277 p else d3276 p
theorem agree3278 (p q : Pattern) (h : Agree support p q) : d3278 p = d3278 q := by
  simp only [d3278, h 162 (by decide), agree3277 p q h, agree3276 p q h]
theorem nonnegative3278 (p : Pattern) : 0 ≤ d3278 p :=
  nonnegative_ite (p 162) (nonnegative3277 p) (nonnegative3276 p)
def d3279 (p : Pattern) : Int := if p 246 then d12 p else d10 p
theorem agree3279 (p q : Pattern) (h : Agree support p q) : d3279 p = d3279 q := by
  simp only [d3279, h 246 (by decide), agree12 p q h, agree10 p q h]
theorem nonnegative3279 (p : Pattern) : 0 ≤ d3279 p :=
  nonnegative_ite (p 246) (nonnegative12 p) (nonnegative10 p)
def d3280 (p : Pattern) : Int := if p 204 then d12 p else d3279 p
theorem agree3280 (p q : Pattern) (h : Agree support p q) : d3280 p = d3280 q := by
  simp only [d3280, h 204 (by decide), agree12 p q h, agree3279 p q h]
theorem nonnegative3280 (p : Pattern) : 0 ≤ d3280 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3279 p)
def d3281 (p : Pattern) : Int := if p 182 then d3280 p else d3279 p
theorem agree3281 (p q : Pattern) (h : Agree support p q) : d3281 p = d3281 q := by
  simp only [d3281, h 182 (by decide), agree3280 p q h, agree3279 p q h]
theorem nonnegative3281 (p : Pattern) : 0 ≤ d3281 p :=
  nonnegative_ite (p 182) (nonnegative3280 p) (nonnegative3279 p)
def d3282 (p : Pattern) : Int := if p 163 then d3281 p else d3241 p
theorem agree3282 (p q : Pattern) (h : Agree support p q) : d3282 p = d3282 q := by
  simp only [d3282, h 163 (by decide), agree3281 p q h, agree3241 p q h]
theorem nonnegative3282 (p : Pattern) : 0 ≤ d3282 p :=
  nonnegative_ite (p 163) (nonnegative3281 p) (nonnegative3241 p)
def d3283 (p : Pattern) : Int := if p 182 then d3258 p else d3257 p
theorem agree3283 (p q : Pattern) (h : Agree support p q) : d3283 p = d3283 q := by
  simp only [d3283, h 182 (by decide), agree3258 p q h, agree3257 p q h]
theorem nonnegative3283 (p : Pattern) : 0 ≤ d3283 p :=
  nonnegative_ite (p 182) (nonnegative3258 p) (nonnegative3257 p)
def d3284 (p : Pattern) : Int := if p 163 then d12 p else d3283 p
theorem agree3284 (p q : Pattern) (h : Agree support p q) : d3284 p = d3284 q := by
  simp only [d3284, h 163 (by decide), agree12 p q h, agree3283 p q h]
theorem nonnegative3284 (p : Pattern) : 0 ≤ d3284 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3283 p)
def d3285 (p : Pattern) : Int := if p 162 then d3284 p else d3282 p
theorem agree3285 (p q : Pattern) (h : Agree support p q) : d3285 p = d3285 q := by
  simp only [d3285, h 162 (by decide), agree3284 p q h, agree3282 p q h]
theorem nonnegative3285 (p : Pattern) : 0 ≤ d3285 p :=
  nonnegative_ite (p 162) (nonnegative3284 p) (nonnegative3282 p)
def d3286 (p : Pattern) : Int := if p 161 then d3285 p else d3278 p
theorem agree3286 (p q : Pattern) (h : Agree support p q) : d3286 p = d3286 q := by
  simp only [d3286, h 161 (by decide), agree3285 p q h, agree3278 p q h]
theorem nonnegative3286 (p : Pattern) : 0 ≤ d3286 p :=
  nonnegative_ite (p 161) (nonnegative3285 p) (nonnegative3278 p)
def d3287 (p : Pattern) : Int := if p 182 then d12 p else d3250 p
theorem agree3287 (p q : Pattern) (h : Agree support p q) : d3287 p = d3287 q := by
  simp only [d3287, h 182 (by decide), agree12 p q h, agree3250 p q h]
theorem nonnegative3287 (p : Pattern) : 0 ≤ d3287 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3250 p)
def d3288 (p : Pattern) : Int := if p 163 then d3287 p else d3255 p
theorem agree3288 (p q : Pattern) (h : Agree support p q) : d3288 p = d3288 q := by
  simp only [d3288, h 163 (by decide), agree3287 p q h, agree3255 p q h]
theorem nonnegative3288 (p : Pattern) : 0 ≤ d3288 p :=
  nonnegative_ite (p 163) (nonnegative3287 p) (nonnegative3255 p)
def d3289 (p : Pattern) : Int := if p 163 then d3265 p else d3260 p
theorem agree3289 (p q : Pattern) (h : Agree support p q) : d3289 p = d3289 q := by
  simp only [d3289, h 163 (by decide), agree3265 p q h, agree3260 p q h]
theorem nonnegative3289 (p : Pattern) : 0 ≤ d3289 p :=
  nonnegative_ite (p 163) (nonnegative3265 p) (nonnegative3260 p)
def d3290 (p : Pattern) : Int := if p 162 then d3289 p else d3288 p
theorem agree3290 (p q : Pattern) (h : Agree support p q) : d3290 p = d3290 q := by
  simp only [d3290, h 162 (by decide), agree3289 p q h, agree3288 p q h]
theorem nonnegative3290 (p : Pattern) : 0 ≤ d3290 p :=
  nonnegative_ite (p 162) (nonnegative3289 p) (nonnegative3288 p)
def d3291 (p : Pattern) : Int := if p 182 then d12 p else d3279 p
theorem agree3291 (p q : Pattern) (h : Agree support p q) : d3291 p = d3291 q := by
  simp only [d3291, h 182 (by decide), agree12 p q h, agree3279 p q h]
theorem nonnegative3291 (p : Pattern) : 0 ≤ d3291 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3279 p)
def d3292 (p : Pattern) : Int := if p 163 then d3291 p else d3260 p
theorem agree3292 (p q : Pattern) (h : Agree support p q) : d3292 p = d3292 q := by
  simp only [d3292, h 163 (by decide), agree3291 p q h, agree3260 p q h]
theorem nonnegative3292 (p : Pattern) : 0 ≤ d3292 p :=
  nonnegative_ite (p 163) (nonnegative3291 p) (nonnegative3260 p)
def d3293 (p : Pattern) : Int := if p 182 then d12 p else d3257 p
theorem agree3293 (p q : Pattern) (h : Agree support p q) : d3293 p = d3293 q := by
  simp only [d3293, h 182 (by decide), agree12 p q h, agree3257 p q h]
theorem nonnegative3293 (p : Pattern) : 0 ≤ d3293 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3257 p)
def d3294 (p : Pattern) : Int := if p 163 then d12 p else d3293 p
theorem agree3294 (p q : Pattern) (h : Agree support p q) : d3294 p = d3294 q := by
  simp only [d3294, h 163 (by decide), agree12 p q h, agree3293 p q h]
theorem nonnegative3294 (p : Pattern) : 0 ≤ d3294 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3293 p)
def d3295 (p : Pattern) : Int := if p 162 then d3294 p else d3292 p
theorem agree3295 (p q : Pattern) (h : Agree support p q) : d3295 p = d3295 q := by
  simp only [d3295, h 162 (by decide), agree3294 p q h, agree3292 p q h]
theorem nonnegative3295 (p : Pattern) : 0 ≤ d3295 p :=
  nonnegative_ite (p 162) (nonnegative3294 p) (nonnegative3292 p)
def d3296 (p : Pattern) : Int := if p 161 then d3295 p else d3290 p
theorem agree3296 (p q : Pattern) (h : Agree support p q) : d3296 p = d3296 q := by
  simp only [d3296, h 161 (by decide), agree3295 p q h, agree3290 p q h]
theorem nonnegative3296 (p : Pattern) : 0 ≤ d3296 p :=
  nonnegative_ite (p 161) (nonnegative3295 p) (nonnegative3290 p)
def d3297 (p : Pattern) : Int := if p 160 then d3296 p else d3286 p
theorem agree3297 (p q : Pattern) (h : Agree support p q) : d3297 p = d3297 q := by
  simp only [d3297, h 160 (by decide), agree3296 p q h, agree3286 p q h]
theorem nonnegative3297 (p : Pattern) : 0 ≤ d3297 p :=
  nonnegative_ite (p 160) (nonnegative3296 p) (nonnegative3286 p)
def d3298 (p : Pattern) : Int := if p 141 then d3297 p else d3269 p
theorem agree3298 (p q : Pattern) (h : Agree support p q) : d3298 p = d3298 q := by
  simp only [d3298, h 141 (by decide), agree3297 p q h, agree3269 p q h]
theorem nonnegative3298 (p : Pattern) : 0 ≤ d3298 p :=
  nonnegative_ite (p 141) (nonnegative3297 p) (nonnegative3269 p)
def d3299 (p : Pattern) : Int := if p 162 then d3242 p else d3238 p
theorem agree3299 (p q : Pattern) (h : Agree support p q) : d3299 p = d3299 q := by
  simp only [d3299, h 162 (by decide), agree3242 p q h, agree3238 p q h]
theorem nonnegative3299 (p : Pattern) : 0 ≤ d3299 p :=
  nonnegative_ite (p 162) (nonnegative3242 p) (nonnegative3238 p)
def d3300 (p : Pattern) : Int := if p 161 then d3248 p else d3299 p
theorem agree3300 (p q : Pattern) (h : Agree support p q) : d3300 p = d3300 q := by
  simp only [d3300, h 161 (by decide), agree3248 p q h, agree3299 p q h]
theorem nonnegative3300 (p : Pattern) : 0 ≤ d3300 p :=
  nonnegative_ite (p 161) (nonnegative3248 p) (nonnegative3299 p)
def d3301 (p : Pattern) : Int := if p 182 then d3254 p else d3253 p
theorem agree3301 (p q : Pattern) (h : Agree support p q) : d3301 p = d3301 q := by
  simp only [d3301, h 182 (by decide), agree3254 p q h, agree3253 p q h]
theorem nonnegative3301 (p : Pattern) : 0 ≤ d3301 p :=
  nonnegative_ite (p 182) (nonnegative3254 p) (nonnegative3253 p)
def d3302 (p : Pattern) : Int := if p 163 then d3301 p else d3275 p
theorem agree3302 (p q : Pattern) (h : Agree support p q) : d3302 p = d3302 q := by
  simp only [d3302, h 163 (by decide), agree3301 p q h, agree3275 p q h]
theorem nonnegative3302 (p : Pattern) : 0 ≤ d3302 p :=
  nonnegative_ite (p 163) (nonnegative3301 p) (nonnegative3275 p)
def d3303 (p : Pattern) : Int := if p 162 then d3284 p else d3302 p
theorem agree3303 (p q : Pattern) (h : Agree support p q) : d3303 p = d3303 q := by
  simp only [d3303, h 162 (by decide), agree3284 p q h, agree3302 p q h]
theorem nonnegative3303 (p : Pattern) : 0 ≤ d3303 p :=
  nonnegative_ite (p 162) (nonnegative3284 p) (nonnegative3302 p)
def d3304 (p : Pattern) : Int := if p 161 then d12 p else d3303 p
theorem agree3304 (p q : Pattern) (h : Agree support p q) : d3304 p = d3304 q := by
  simp only [d3304, h 161 (by decide), agree12 p q h, agree3303 p q h]
theorem nonnegative3304 (p : Pattern) : 0 ≤ d3304 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3303 p)
def d3305 (p : Pattern) : Int := if p 160 then d3304 p else d3300 p
theorem agree3305 (p q : Pattern) (h : Agree support p q) : d3305 p = d3305 q := by
  simp only [d3305, h 160 (by decide), agree3304 p q h, agree3300 p q h]
theorem nonnegative3305 (p : Pattern) : 0 ≤ d3305 p :=
  nonnegative_ite (p 160) (nonnegative3304 p) (nonnegative3300 p)
def d3306 (p : Pattern) : Int := if p 163 then d3275 p else d3238 p
theorem agree3306 (p q : Pattern) (h : Agree support p q) : d3306 p = d3306 q := by
  simp only [d3306, h 163 (by decide), agree3275 p q h, agree3238 p q h]
theorem nonnegative3306 (p : Pattern) : 0 ≤ d3306 p :=
  nonnegative_ite (p 163) (nonnegative3275 p) (nonnegative3238 p)
def d3307 (p : Pattern) : Int := if p 162 then d3277 p else d3306 p
theorem agree3307 (p q : Pattern) (h : Agree support p q) : d3307 p = d3307 q := by
  simp only [d3307, h 162 (by decide), agree3277 p q h, agree3306 p q h]
theorem nonnegative3307 (p : Pattern) : 0 ≤ d3307 p :=
  nonnegative_ite (p 162) (nonnegative3277 p) (nonnegative3306 p)
def d3308 (p : Pattern) : Int := if p 161 then d3285 p else d3307 p
theorem agree3308 (p q : Pattern) (h : Agree support p q) : d3308 p = d3308 q := by
  simp only [d3308, h 161 (by decide), agree3285 p q h, agree3307 p q h]
theorem nonnegative3308 (p : Pattern) : 0 ≤ d3308 p :=
  nonnegative_ite (p 161) (nonnegative3285 p) (nonnegative3307 p)
def d3309 (p : Pattern) : Int := if p 163 then d12 p else d3301 p
theorem agree3309 (p q : Pattern) (h : Agree support p q) : d3309 p = d3309 q := by
  simp only [d3309, h 163 (by decide), agree12 p q h, agree3301 p q h]
theorem nonnegative3309 (p : Pattern) : 0 ≤ d3309 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3301 p)
def d3310 (p : Pattern) : Int := if p 162 then d12 p else d3309 p
theorem agree3310 (p q : Pattern) (h : Agree support p q) : d3310 p = d3310 q := by
  simp only [d3310, h 162 (by decide), agree12 p q h, agree3309 p q h]
theorem nonnegative3310 (p : Pattern) : 0 ≤ d3310 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3309 p)
def d3311 (p : Pattern) : Int := if p 161 then d12 p else d3310 p
theorem agree3311 (p q : Pattern) (h : Agree support p q) : d3311 p = d3311 q := by
  simp only [d3311, h 161 (by decide), agree12 p q h, agree3310 p q h]
theorem nonnegative3311 (p : Pattern) : 0 ≤ d3311 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3310 p)
def d3312 (p : Pattern) : Int := if p 160 then d3311 p else d3308 p
theorem agree3312 (p q : Pattern) (h : Agree support p q) : d3312 p = d3312 q := by
  simp only [d3312, h 160 (by decide), agree3311 p q h, agree3308 p q h]
theorem nonnegative3312 (p : Pattern) : 0 ≤ d3312 p :=
  nonnegative_ite (p 160) (nonnegative3311 p) (nonnegative3308 p)
def d3313 (p : Pattern) : Int := if p 141 then d3312 p else d3305 p
theorem agree3313 (p q : Pattern) (h : Agree support p q) : d3313 p = d3313 q := by
  simp only [d3313, h 141 (by decide), agree3312 p q h, agree3305 p q h]
theorem nonnegative3313 (p : Pattern) : 0 ≤ d3313 p :=
  nonnegative_ite (p 141) (nonnegative3312 p) (nonnegative3305 p)
def d3314 (p : Pattern) : Int := if p 138 then d3313 p else d3298 p
theorem agree3314 (p q : Pattern) (h : Agree support p q) : d3314 p = d3314 q := by
  simp only [d3314, h 138 (by decide), agree3313 p q h, agree3298 p q h]
theorem nonnegative3314 (p : Pattern) : 0 ≤ d3314 p :=
  nonnegative_ite (p 138) (nonnegative3313 p) (nonnegative3298 p)
def d3315 (p : Pattern) : Int := if p 163 then d3283 p else d3246 p
theorem agree3315 (p q : Pattern) (h : Agree support p q) : d3315 p = d3315 q := by
  simp only [d3315, h 163 (by decide), agree3283 p q h, agree3246 p q h]
theorem nonnegative3315 (p : Pattern) : 0 ≤ d3315 p :=
  nonnegative_ite (p 163) (nonnegative3283 p) (nonnegative3246 p)
def d3316 (p : Pattern) : Int := if p 162 then d3284 p else d3315 p
theorem agree3316 (p q : Pattern) (h : Agree support p q) : d3316 p = d3316 q := by
  simp only [d3316, h 162 (by decide), agree3284 p q h, agree3315 p q h]
theorem nonnegative3316 (p : Pattern) : 0 ≤ d3316 p :=
  nonnegative_ite (p 162) (nonnegative3284 p) (nonnegative3315 p)
def d3317 (p : Pattern) : Int := if p 162 then d12 p else d3284 p
theorem agree3317 (p q : Pattern) (h : Agree support p q) : d3317 p = d3317 q := by
  simp only [d3317, h 162 (by decide), agree12 p q h, agree3284 p q h]
theorem nonnegative3317 (p : Pattern) : 0 ≤ d3317 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3284 p)
def d3318 (p : Pattern) : Int := if p 161 then d3317 p else d3316 p
theorem agree3318 (p q : Pattern) (h : Agree support p q) : d3318 p = d3318 q := by
  simp only [d3318, h 161 (by decide), agree3317 p q h, agree3316 p q h]
theorem nonnegative3318 (p : Pattern) : 0 ≤ d3318 p :=
  nonnegative_ite (p 161) (nonnegative3317 p) (nonnegative3316 p)
def d3319 (p : Pattern) : Int := if p 161 then d12 p else d3317 p
theorem agree3319 (p q : Pattern) (h : Agree support p q) : d3319 p = d3319 q := by
  simp only [d3319, h 161 (by decide), agree12 p q h, agree3317 p q h]
theorem nonnegative3319 (p : Pattern) : 0 ≤ d3319 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3317 p)
def d3320 (p : Pattern) : Int := if p 160 then d3319 p else d3318 p
theorem agree3320 (p q : Pattern) (h : Agree support p q) : d3320 p = d3320 q := by
  simp only [d3320, h 160 (by decide), agree3319 p q h, agree3318 p q h]
theorem nonnegative3320 (p : Pattern) : 0 ≤ d3320 p :=
  nonnegative_ite (p 160) (nonnegative3319 p) (nonnegative3318 p)
def d3321 (p : Pattern) : Int := if p 160 then d12 p else d3319 p
theorem agree3321 (p q : Pattern) (h : Agree support p q) : d3321 p = d3321 q := by
  simp only [d3321, h 160 (by decide), agree12 p q h, agree3319 p q h]
theorem nonnegative3321 (p : Pattern) : 0 ≤ d3321 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative3319 p)
def d3322 (p : Pattern) : Int := if p 141 then d3321 p else d3320 p
theorem agree3322 (p q : Pattern) (h : Agree support p q) : d3322 p = d3322 q := by
  simp only [d3322, h 141 (by decide), agree3321 p q h, agree3320 p q h]
theorem nonnegative3322 (p : Pattern) : 0 ≤ d3322 p :=
  nonnegative_ite (p 141) (nonnegative3321 p) (nonnegative3320 p)
def d3323 (p : Pattern) : Int := if p 138 then d3322 p else d3313 p
theorem agree3323 (p q : Pattern) (h : Agree support p q) : d3323 p = d3323 q := by
  simp only [d3323, h 138 (by decide), agree3322 p q h, agree3313 p q h]
theorem nonnegative3323 (p : Pattern) : 0 ≤ d3323 p :=
  nonnegative_ite (p 138) (nonnegative3322 p) (nonnegative3313 p)
def d3324 (p : Pattern) : Int := if p 116 then d3323 p else d3314 p
theorem agree3324 (p q : Pattern) (h : Agree support p q) : d3324 p = d3324 q := by
  simp only [d3324, h 116 (by decide), agree3323 p q h, agree3314 p q h]
theorem nonnegative3324 (p : Pattern) : 0 ≤ d3324 p :=
  nonnegative_ite (p 116) (nonnegative3323 p) (nonnegative3314 p)
def d3325 (p : Pattern) : Int := if p 163 then d3238 p else d3236 p
theorem agree3325 (p q : Pattern) (h : Agree support p q) : d3325 p = d3325 q := by
  simp only [d3325, h 163 (by decide), agree3238 p q h, agree3236 p q h]
theorem nonnegative3325 (p : Pattern) : 0 ≤ d3325 p :=
  nonnegative_ite (p 163) (nonnegative3238 p) (nonnegative3236 p)
def d3326 (p : Pattern) : Int := if p 162 then d3242 p else d3325 p
theorem agree3326 (p q : Pattern) (h : Agree support p q) : d3326 p = d3326 q := by
  simp only [d3326, h 162 (by decide), agree3242 p q h, agree3325 p q h]
theorem nonnegative3326 (p : Pattern) : 0 ≤ d3326 p :=
  nonnegative_ite (p 162) (nonnegative3242 p) (nonnegative3325 p)
def d3327 (p : Pattern) : Int := if p 161 then d3248 p else d3326 p
theorem agree3327 (p q : Pattern) (h : Agree support p q) : d3327 p = d3327 q := by
  simp only [d3327, h 161 (by decide), agree3248 p q h, agree3326 p q h]
theorem nonnegative3327 (p : Pattern) : 0 ≤ d3327 p :=
  nonnegative_ite (p 161) (nonnegative3248 p) (nonnegative3326 p)
def d3328 (p : Pattern) : Int := if p 160 then d3268 p else d3327 p
theorem agree3328 (p q : Pattern) (h : Agree support p q) : d3328 p = d3328 q := by
  simp only [d3328, h 160 (by decide), agree3268 p q h, agree3327 p q h]
theorem nonnegative3328 (p : Pattern) : 0 ≤ d3328 p :=
  nonnegative_ite (p 160) (nonnegative3268 p) (nonnegative3327 p)
def d3329 (p : Pattern) : Int := if p 160 then d3296 p else d3308 p
theorem agree3329 (p q : Pattern) (h : Agree support p q) : d3329 p = d3329 q := by
  simp only [d3329, h 160 (by decide), agree3296 p q h, agree3308 p q h]
theorem nonnegative3329 (p : Pattern) : 0 ≤ d3329 p :=
  nonnegative_ite (p 160) (nonnegative3296 p) (nonnegative3308 p)
def d3330 (p : Pattern) : Int := if p 141 then d3329 p else d3328 p
theorem agree3330 (p q : Pattern) (h : Agree support p q) : d3330 p = d3330 q := by
  simp only [d3330, h 141 (by decide), agree3329 p q h, agree3328 p q h]
theorem nonnegative3330 (p : Pattern) : 0 ≤ d3330 p :=
  nonnegative_ite (p 141) (nonnegative3329 p) (nonnegative3328 p)
def d3331 (p : Pattern) : Int := if p 138 then d3313 p else d3330 p
theorem agree3331 (p q : Pattern) (h : Agree support p q) : d3331 p = d3331 q := by
  simp only [d3331, h 138 (by decide), agree3313 p q h, agree3330 p q h]
theorem nonnegative3331 (p : Pattern) : 0 ≤ d3331 p :=
  nonnegative_ite (p 138) (nonnegative3313 p) (nonnegative3330 p)
def d3332 (p : Pattern) : Int := if p 138 then d12 p else d3313 p
theorem agree3332 (p q : Pattern) (h : Agree support p q) : d3332 p = d3332 q := by
  simp only [d3332, h 138 (by decide), agree12 p q h, agree3313 p q h]
theorem nonnegative3332 (p : Pattern) : 0 ≤ d3332 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative3313 p)
def d3333 (p : Pattern) : Int := if p 116 then d3332 p else d3331 p
theorem agree3333 (p q : Pattern) (h : Agree support p q) : d3333 p = d3333 q := by
  simp only [d3333, h 116 (by decide), agree3332 p q h, agree3331 p q h]
theorem nonnegative3333 (p : Pattern) : 0 ≤ d3333 p :=
  nonnegative_ite (p 116) (nonnegative3332 p) (nonnegative3331 p)
def d3334 (p : Pattern) : Int := if p 115 then d3333 p else d3324 p
theorem agree3334 (p q : Pattern) (h : Agree support p q) : d3334 p = d3334 q := by
  simp only [d3334, h 115 (by decide), agree3333 p q h, agree3324 p q h]
theorem nonnegative3334 (p : Pattern) : 0 ≤ d3334 p :=
  nonnegative_ite (p 115) (nonnegative3333 p) (nonnegative3324 p)
def d3335 (p : Pattern) : Int := if p 246 then d23 p else d0 p
theorem agree3335 (p q : Pattern) (h : Agree support p q) : d3335 p = d3335 q := by
  simp only [d3335, h 246 (by decide), agree23 p q h, agree0 p q h]
theorem nonnegative3335 (p : Pattern) : 0 ≤ d3335 p :=
  nonnegative_ite (p 246) (nonnegative23 p) (nonnegative0 p)
def d3336 (p : Pattern) : Int := if p 225 then d3226 p else d3335 p
theorem agree3336 (p q : Pattern) (h : Agree support p q) : d3336 p = d3336 q := by
  simp only [d3336, h 225 (by decide), agree3226 p q h, agree3335 p q h]
theorem nonnegative3336 (p : Pattern) : 0 ≤ d3336 p :=
  nonnegative_ite (p 225) (nonnegative3226 p) (nonnegative3335 p)
def d3337 (p : Pattern) : Int := if p 224 then d3226 p else d3336 p
theorem agree3337 (p q : Pattern) (h : Agree support p q) : d3337 p = d3337 q := by
  simp only [d3337, h 224 (by decide), agree3226 p q h, agree3336 p q h]
theorem nonnegative3337 (p : Pattern) : 0 ≤ d3337 p :=
  nonnegative_ite (p 224) (nonnegative3226 p) (nonnegative3336 p)
def d3338 (p : Pattern) : Int := if p 204 then d3226 p else d3337 p
theorem agree3338 (p q : Pattern) (h : Agree support p q) : d3338 p = d3338 q := by
  simp only [d3338, h 204 (by decide), agree3226 p q h, agree3337 p q h]
theorem nonnegative3338 (p : Pattern) : 0 ≤ d3338 p :=
  nonnegative_ite (p 204) (nonnegative3226 p) (nonnegative3337 p)
def d3339 (p : Pattern) : Int := if p 182 then d3230 p else d3338 p
theorem agree3339 (p q : Pattern) (h : Agree support p q) : d3339 p = d3339 q := by
  simp only [d3339, h 182 (by decide), agree3230 p q h, agree3338 p q h]
theorem nonnegative3339 (p : Pattern) : 0 ≤ d3339 p :=
  nonnegative_ite (p 182) (nonnegative3230 p) (nonnegative3338 p)
def d3340 (p : Pattern) : Int := if p 163 then d3238 p else d3339 p
theorem agree3340 (p q : Pattern) (h : Agree support p q) : d3340 p = d3340 q := by
  simp only [d3340, h 163 (by decide), agree3238 p q h, agree3339 p q h]
theorem nonnegative3340 (p : Pattern) : 0 ≤ d3340 p :=
  nonnegative_ite (p 163) (nonnegative3238 p) (nonnegative3339 p)
def d3341 (p : Pattern) : Int := if p 162 then d3242 p else d3340 p
theorem agree3341 (p q : Pattern) (h : Agree support p q) : d3341 p = d3341 q := by
  simp only [d3341, h 162 (by decide), agree3242 p q h, agree3340 p q h]
theorem nonnegative3341 (p : Pattern) : 0 ≤ d3341 p :=
  nonnegative_ite (p 162) (nonnegative3242 p) (nonnegative3340 p)
def d3342 (p : Pattern) : Int := if p 161 then d3248 p else d3341 p
theorem agree3342 (p q : Pattern) (h : Agree support p q) : d3342 p = d3342 q := by
  simp only [d3342, h 161 (by decide), agree3248 p q h, agree3341 p q h]
theorem nonnegative3342 (p : Pattern) : 0 ≤ d3342 p :=
  nonnegative_ite (p 161) (nonnegative3248 p) (nonnegative3341 p)
def d3343 (p : Pattern) : Int := if p 160 then d3268 p else d3342 p
theorem agree3343 (p q : Pattern) (h : Agree support p q) : d3343 p = d3343 q := by
  simp only [d3343, h 160 (by decide), agree3268 p q h, agree3342 p q h]
theorem nonnegative3343 (p : Pattern) : 0 ≤ d3343 p :=
  nonnegative_ite (p 160) (nonnegative3268 p) (nonnegative3342 p)
def d3344 (p : Pattern) : Int := if p 163 then d3275 p else d3236 p
theorem agree3344 (p q : Pattern) (h : Agree support p q) : d3344 p = d3344 q := by
  simp only [d3344, h 163 (by decide), agree3275 p q h, agree3236 p q h]
theorem nonnegative3344 (p : Pattern) : 0 ≤ d3344 p :=
  nonnegative_ite (p 163) (nonnegative3275 p) (nonnegative3236 p)
def d3345 (p : Pattern) : Int := if p 162 then d3277 p else d3344 p
theorem agree3345 (p q : Pattern) (h : Agree support p q) : d3345 p = d3345 q := by
  simp only [d3345, h 162 (by decide), agree3277 p q h, agree3344 p q h]
theorem nonnegative3345 (p : Pattern) : 0 ≤ d3345 p :=
  nonnegative_ite (p 162) (nonnegative3277 p) (nonnegative3344 p)
def d3346 (p : Pattern) : Int := if p 161 then d3285 p else d3345 p
theorem agree3346 (p q : Pattern) (h : Agree support p q) : d3346 p = d3346 q := by
  simp only [d3346, h 161 (by decide), agree3285 p q h, agree3345 p q h]
theorem nonnegative3346 (p : Pattern) : 0 ≤ d3346 p :=
  nonnegative_ite (p 161) (nonnegative3285 p) (nonnegative3345 p)
def d3347 (p : Pattern) : Int := if p 160 then d3296 p else d3346 p
theorem agree3347 (p q : Pattern) (h : Agree support p q) : d3347 p = d3347 q := by
  simp only [d3347, h 160 (by decide), agree3296 p q h, agree3346 p q h]
theorem nonnegative3347 (p : Pattern) : 0 ≤ d3347 p :=
  nonnegative_ite (p 160) (nonnegative3296 p) (nonnegative3346 p)
def d3348 (p : Pattern) : Int := if p 141 then d3347 p else d3343 p
theorem agree3348 (p q : Pattern) (h : Agree support p q) : d3348 p = d3348 q := by
  simp only [d3348, h 141 (by decide), agree3347 p q h, agree3343 p q h]
theorem nonnegative3348 (p : Pattern) : 0 ≤ d3348 p :=
  nonnegative_ite (p 141) (nonnegative3347 p) (nonnegative3343 p)
def d3349 (p : Pattern) : Int := if p 138 then d3313 p else d3348 p
theorem agree3349 (p q : Pattern) (h : Agree support p q) : d3349 p = d3349 q := by
  simp only [d3349, h 138 (by decide), agree3313 p q h, agree3348 p q h]
theorem nonnegative3349 (p : Pattern) : 0 ≤ d3349 p :=
  nonnegative_ite (p 138) (nonnegative3313 p) (nonnegative3348 p)
def d3350 (p : Pattern) : Int := if p 116 then d3323 p else d3349 p
theorem agree3350 (p q : Pattern) (h : Agree support p q) : d3350 p = d3350 q := by
  simp only [d3350, h 116 (by decide), agree3323 p q h, agree3349 p q h]
theorem nonnegative3350 (p : Pattern) : 0 ≤ d3350 p :=
  nonnegative_ite (p 116) (nonnegative3323 p) (nonnegative3349 p)
def d3351 (p : Pattern) : Int := if p 160 then d3268 p else d3300 p
theorem agree3351 (p q : Pattern) (h : Agree support p q) : d3351 p = d3351 q := by
  simp only [d3351, h 160 (by decide), agree3268 p q h, agree3300 p q h]
theorem nonnegative3351 (p : Pattern) : 0 ≤ d3351 p :=
  nonnegative_ite (p 160) (nonnegative3268 p) (nonnegative3300 p)
def d3352 (p : Pattern) : Int := if p 141 then d3329 p else d3351 p
theorem agree3352 (p q : Pattern) (h : Agree support p q) : d3352 p = d3352 q := by
  simp only [d3352, h 141 (by decide), agree3329 p q h, agree3351 p q h]
theorem nonnegative3352 (p : Pattern) : 0 ≤ d3352 p :=
  nonnegative_ite (p 141) (nonnegative3329 p) (nonnegative3351 p)
def d3353 (p : Pattern) : Int := if p 138 then d3313 p else d3352 p
theorem agree3353 (p q : Pattern) (h : Agree support p q) : d3353 p = d3353 q := by
  simp only [d3353, h 138 (by decide), agree3313 p q h, agree3352 p q h]
theorem nonnegative3353 (p : Pattern) : 0 ≤ d3353 p :=
  nonnegative_ite (p 138) (nonnegative3313 p) (nonnegative3352 p)
def d3354 (p : Pattern) : Int := if p 116 then d3332 p else d3353 p
theorem agree3354 (p q : Pattern) (h : Agree support p q) : d3354 p = d3354 q := by
  simp only [d3354, h 116 (by decide), agree3332 p q h, agree3353 p q h]
theorem nonnegative3354 (p : Pattern) : 0 ≤ d3354 p :=
  nonnegative_ite (p 116) (nonnegative3332 p) (nonnegative3353 p)
def d3355 (p : Pattern) : Int := if p 115 then d3354 p else d3350 p
theorem agree3355 (p q : Pattern) (h : Agree support p q) : d3355 p = d3355 q := by
  simp only [d3355, h 115 (by decide), agree3354 p q h, agree3350 p q h]
theorem nonnegative3355 (p : Pattern) : 0 ≤ d3355 p :=
  nonnegative_ite (p 115) (nonnegative3354 p) (nonnegative3350 p)
def d3356 (p : Pattern) : Int := if p 71 then d3355 p else d3334 p
theorem agree3356 (p q : Pattern) (h : Agree support p q) : d3356 p = d3356 q := by
  simp only [d3356, h 71 (by decide), agree3355 p q h, agree3334 p q h]
theorem nonnegative3356 (p : Pattern) : 0 ≤ d3356 p :=
  nonnegative_ite (p 71) (nonnegative3355 p) (nonnegative3334 p)
def d3357 (p : Pattern) : Int := if p 246 then d23 p else d1 p
theorem agree3357 (p q : Pattern) (h : Agree support p q) : d3357 p = d3357 q := by
  simp only [d3357, h 246 (by decide), agree23 p q h, agree1 p q h]
theorem nonnegative3357 (p : Pattern) : 0 ≤ d3357 p :=
  nonnegative_ite (p 246) (nonnegative23 p) (nonnegative1 p)
def d3358 (p : Pattern) : Int := if p 246 then d12 p else d1 p
theorem agree3358 (p q : Pattern) (h : Agree support p q) : d3358 p = d3358 q := by
  simp only [d3358, h 246 (by decide), agree12 p q h, agree1 p q h]
theorem nonnegative3358 (p : Pattern) : 0 ≤ d3358 p :=
  nonnegative_ite (p 246) (nonnegative12 p) (nonnegative1 p)
def d3359 (p : Pattern) : Int := if p 225 then d3358 p else d3357 p
theorem agree3359 (p q : Pattern) (h : Agree support p q) : d3359 p = d3359 q := by
  simp only [d3359, h 225 (by decide), agree3358 p q h, agree3357 p q h]
theorem nonnegative3359 (p : Pattern) : 0 ≤ d3359 p :=
  nonnegative_ite (p 225) (nonnegative3358 p) (nonnegative3357 p)
end NetHack.Sokoban22Refined85
