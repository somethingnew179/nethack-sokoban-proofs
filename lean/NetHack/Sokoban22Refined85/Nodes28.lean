/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes27
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d3360 (p : Pattern) : Int := if p 224 then d3358 p else d3359 p
theorem agree3360 (p q : Pattern) (h : Agree support p q) : d3360 p = d3360 q := by
  simp only [d3360, h 224 (by decide), agree3358 p q h, agree3359 p q h]
theorem nonnegative3360 (p : Pattern) : 0 ≤ d3360 p :=
  nonnegative_ite (p 224) (nonnegative3358 p) (nonnegative3359 p)
def d3361 (p : Pattern) : Int := if p 204 then d3358 p else d3360 p
theorem agree3361 (p q : Pattern) (h : Agree support p q) : d3361 p = d3361 q := by
  simp only [d3361, h 204 (by decide), agree3358 p q h, agree3360 p q h]
theorem nonnegative3361 (p : Pattern) : 0 ≤ d3361 p :=
  nonnegative_ite (p 204) (nonnegative3358 p) (nonnegative3360 p)
def d3362 (p : Pattern) : Int := if p 204 then d12 p else d3358 p
theorem agree3362 (p q : Pattern) (h : Agree support p q) : d3362 p = d3362 q := by
  simp only [d3362, h 204 (by decide), agree12 p q h, agree3358 p q h]
theorem nonnegative3362 (p : Pattern) : 0 ≤ d3362 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3358 p)
def d3363 (p : Pattern) : Int := if p 182 then d3362 p else d3361 p
theorem agree3363 (p q : Pattern) (h : Agree support p q) : d3363 p = d3363 q := by
  simp only [d3363, h 182 (by decide), agree3362 p q h, agree3361 p q h]
theorem nonnegative3363 (p : Pattern) : 0 ≤ d3363 p :=
  nonnegative_ite (p 182) (nonnegative3362 p) (nonnegative3361 p)
def d3364 (p : Pattern) : Int := if p 182 then d3362 p else d3358 p
theorem agree3364 (p q : Pattern) (h : Agree support p q) : d3364 p = d3364 q := by
  simp only [d3364, h 182 (by decide), agree3362 p q h, agree3358 p q h]
theorem nonnegative3364 (p : Pattern) : 0 ≤ d3364 p :=
  nonnegative_ite (p 182) (nonnegative3362 p) (nonnegative3358 p)
def d3365 (p : Pattern) : Int := if p 163 then d3364 p else d3363 p
theorem agree3365 (p q : Pattern) (h : Agree support p q) : d3365 p = d3365 q := by
  simp only [d3365, h 163 (by decide), agree3364 p q h, agree3363 p q h]
theorem nonnegative3365 (p : Pattern) : 0 ≤ d3365 p :=
  nonnegative_ite (p 163) (nonnegative3364 p) (nonnegative3363 p)
def d3366 (p : Pattern) : Int := if p 246 then d12 p else d5 p
theorem agree3366 (p q : Pattern) (h : Agree support p q) : d3366 p = d3366 q := by
  simp only [d3366, h 246 (by decide), agree12 p q h, agree5 p q h]
theorem nonnegative3366 (p : Pattern) : 0 ≤ d3366 p :=
  nonnegative_ite (p 246) (nonnegative12 p) (nonnegative5 p)
def d3367 (p : Pattern) : Int := if p 204 then d12 p else d3366 p
theorem agree3367 (p q : Pattern) (h : Agree support p q) : d3367 p = d3367 q := by
  simp only [d3367, h 204 (by decide), agree12 p q h, agree3366 p q h]
theorem nonnegative3367 (p : Pattern) : 0 ≤ d3367 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3366 p)
def d3368 (p : Pattern) : Int := if p 182 then d3367 p else d3366 p
theorem agree3368 (p q : Pattern) (h : Agree support p q) : d3368 p = d3368 q := by
  simp only [d3368, h 182 (by decide), agree3367 p q h, agree3366 p q h]
theorem nonnegative3368 (p : Pattern) : 0 ≤ d3368 p :=
  nonnegative_ite (p 182) (nonnegative3367 p) (nonnegative3366 p)
def d3369 (p : Pattern) : Int := if p 163 then d3368 p else d3364 p
theorem agree3369 (p q : Pattern) (h : Agree support p q) : d3369 p = d3369 q := by
  simp only [d3369, h 163 (by decide), agree3368 p q h, agree3364 p q h]
theorem nonnegative3369 (p : Pattern) : 0 ≤ d3369 p :=
  nonnegative_ite (p 163) (nonnegative3368 p) (nonnegative3364 p)
def d3370 (p : Pattern) : Int := if p 162 then d3369 p else d3365 p
theorem agree3370 (p q : Pattern) (h : Agree support p q) : d3370 p = d3370 q := by
  simp only [d3370, h 162 (by decide), agree3369 p q h, agree3365 p q h]
theorem nonnegative3370 (p : Pattern) : 0 ≤ d3370 p :=
  nonnegative_ite (p 162) (nonnegative3369 p) (nonnegative3365 p)
def d3371 (p : Pattern) : Int := if p 163 then d12 p else d3281 p
theorem agree3371 (p q : Pattern) (h : Agree support p q) : d3371 p = d3371 q := by
  simp only [d3371, h 163 (by decide), agree12 p q h, agree3281 p q h]
theorem nonnegative3371 (p : Pattern) : 0 ≤ d3371 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3281 p)
def d3372 (p : Pattern) : Int := if p 162 then d3371 p else d3369 p
theorem agree3372 (p q : Pattern) (h : Agree support p q) : d3372 p = d3372 q := by
  simp only [d3372, h 162 (by decide), agree3371 p q h, agree3369 p q h]
theorem nonnegative3372 (p : Pattern) : 0 ≤ d3372 p :=
  nonnegative_ite (p 162) (nonnegative3371 p) (nonnegative3369 p)
def d3373 (p : Pattern) : Int := if p 161 then d3372 p else d3370 p
theorem agree3373 (p q : Pattern) (h : Agree support p q) : d3373 p = d3373 q := by
  simp only [d3373, h 161 (by decide), agree3372 p q h, agree3370 p q h]
theorem nonnegative3373 (p : Pattern) : 0 ≤ d3373 p :=
  nonnegative_ite (p 161) (nonnegative3372 p) (nonnegative3370 p)
def d3374 (p : Pattern) : Int := if p 246 then d12 p else d3 p
theorem agree3374 (p q : Pattern) (h : Agree support p q) : d3374 p = d3374 q := by
  simp only [d3374, h 246 (by decide), agree12 p q h, agree3 p q h]
theorem nonnegative3374 (p : Pattern) : 0 ≤ d3374 p :=
  nonnegative_ite (p 246) (nonnegative12 p) (nonnegative3 p)
def d3375 (p : Pattern) : Int := if p 204 then d12 p else d3374 p
theorem agree3375 (p q : Pattern) (h : Agree support p q) : d3375 p = d3375 q := by
  simp only [d3375, h 204 (by decide), agree12 p q h, agree3374 p q h]
theorem nonnegative3375 (p : Pattern) : 0 ≤ d3375 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3374 p)
def d3376 (p : Pattern) : Int := if p 182 then d3375 p else d3358 p
theorem agree3376 (p q : Pattern) (h : Agree support p q) : d3376 p = d3376 q := by
  simp only [d3376, h 182 (by decide), agree3375 p q h, agree3358 p q h]
theorem nonnegative3376 (p : Pattern) : 0 ≤ d3376 p :=
  nonnegative_ite (p 182) (nonnegative3375 p) (nonnegative3358 p)
def d3377 (p : Pattern) : Int := if p 246 then d12 p else d7 p
theorem agree3377 (p q : Pattern) (h : Agree support p q) : d3377 p = d3377 q := by
  simp only [d3377, h 246 (by decide), agree12 p q h, agree7 p q h]
theorem nonnegative3377 (p : Pattern) : 0 ≤ d3377 p :=
  nonnegative_ite (p 246) (nonnegative12 p) (nonnegative7 p)
def d3378 (p : Pattern) : Int := if p 204 then d12 p else d3377 p
theorem agree3378 (p q : Pattern) (h : Agree support p q) : d3378 p = d3378 q := by
  simp only [d3378, h 204 (by decide), agree12 p q h, agree3377 p q h]
theorem nonnegative3378 (p : Pattern) : 0 ≤ d3378 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3377 p)
def d3379 (p : Pattern) : Int := if p 182 then d3378 p else d3358 p
theorem agree3379 (p q : Pattern) (h : Agree support p q) : d3379 p = d3379 q := by
  simp only [d3379, h 182 (by decide), agree3378 p q h, agree3358 p q h]
theorem nonnegative3379 (p : Pattern) : 0 ≤ d3379 p :=
  nonnegative_ite (p 182) (nonnegative3378 p) (nonnegative3358 p)
def d3380 (p : Pattern) : Int := if p 163 then d3379 p else d3376 p
theorem agree3380 (p q : Pattern) (h : Agree support p q) : d3380 p = d3380 q := by
  simp only [d3380, h 163 (by decide), agree3379 p q h, agree3376 p q h]
theorem nonnegative3380 (p : Pattern) : 0 ≤ d3380 p :=
  nonnegative_ite (p 163) (nonnegative3379 p) (nonnegative3376 p)
def d3381 (p : Pattern) : Int := if p 182 then d12 p else d3358 p
theorem agree3381 (p q : Pattern) (h : Agree support p q) : d3381 p = d3381 q := by
  simp only [d3381, h 182 (by decide), agree12 p q h, agree3358 p q h]
theorem nonnegative3381 (p : Pattern) : 0 ≤ d3381 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3358 p)
def d3382 (p : Pattern) : Int := if p 182 then d12 p else d3366 p
theorem agree3382 (p q : Pattern) (h : Agree support p q) : d3382 p = d3382 q := by
  simp only [d3382, h 182 (by decide), agree12 p q h, agree3366 p q h]
theorem nonnegative3382 (p : Pattern) : 0 ≤ d3382 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3366 p)
def d3383 (p : Pattern) : Int := if p 163 then d3382 p else d3381 p
theorem agree3383 (p q : Pattern) (h : Agree support p q) : d3383 p = d3383 q := by
  simp only [d3383, h 163 (by decide), agree3382 p q h, agree3381 p q h]
theorem nonnegative3383 (p : Pattern) : 0 ≤ d3383 p :=
  nonnegative_ite (p 163) (nonnegative3382 p) (nonnegative3381 p)
def d3384 (p : Pattern) : Int := if p 162 then d3383 p else d3380 p
theorem agree3384 (p q : Pattern) (h : Agree support p q) : d3384 p = d3384 q := by
  simp only [d3384, h 162 (by decide), agree3383 p q h, agree3380 p q h]
theorem nonnegative3384 (p : Pattern) : 0 ≤ d3384 p :=
  nonnegative_ite (p 162) (nonnegative3383 p) (nonnegative3380 p)
def d3385 (p : Pattern) : Int := if p 163 then d12 p else d3291 p
theorem agree3385 (p q : Pattern) (h : Agree support p q) : d3385 p = d3385 q := by
  simp only [d3385, h 163 (by decide), agree12 p q h, agree3291 p q h]
theorem nonnegative3385 (p : Pattern) : 0 ≤ d3385 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3291 p)
def d3386 (p : Pattern) : Int := if p 162 then d3385 p else d3383 p
theorem agree3386 (p q : Pattern) (h : Agree support p q) : d3386 p = d3386 q := by
  simp only [d3386, h 162 (by decide), agree3385 p q h, agree3383 p q h]
theorem nonnegative3386 (p : Pattern) : 0 ≤ d3386 p :=
  nonnegative_ite (p 162) (nonnegative3385 p) (nonnegative3383 p)
def d3387 (p : Pattern) : Int := if p 161 then d3386 p else d3384 p
theorem agree3387 (p q : Pattern) (h : Agree support p q) : d3387 p = d3387 q := by
  simp only [d3387, h 161 (by decide), agree3386 p q h, agree3384 p q h]
theorem nonnegative3387 (p : Pattern) : 0 ≤ d3387 p :=
  nonnegative_ite (p 161) (nonnegative3386 p) (nonnegative3384 p)
def d3388 (p : Pattern) : Int := if p 160 then d3387 p else d3373 p
theorem agree3388 (p q : Pattern) (h : Agree support p q) : d3388 p = d3388 q := by
  simp only [d3388, h 160 (by decide), agree3387 p q h, agree3373 p q h]
theorem nonnegative3388 (p : Pattern) : 0 ≤ d3388 p :=
  nonnegative_ite (p 160) (nonnegative3387 p) (nonnegative3373 p)
def d3389 (p : Pattern) : Int := if p 246 then d39 p else d1 p
theorem agree3389 (p q : Pattern) (h : Agree support p q) : d3389 p = d3389 q := by
  simp only [d3389, h 246 (by decide), agree39 p q h, agree1 p q h]
theorem nonnegative3389 (p : Pattern) : 0 ≤ d3389 p :=
  nonnegative_ite (p 246) (nonnegative39 p) (nonnegative1 p)
def d3390 (p : Pattern) : Int := if p 225 then d3358 p else d3389 p
theorem agree3390 (p q : Pattern) (h : Agree support p q) : d3390 p = d3390 q := by
  simp only [d3390, h 225 (by decide), agree3358 p q h, agree3389 p q h]
theorem nonnegative3390 (p : Pattern) : 0 ≤ d3390 p :=
  nonnegative_ite (p 225) (nonnegative3358 p) (nonnegative3389 p)
def d3391 (p : Pattern) : Int := if p 224 then d3358 p else d3390 p
theorem agree3391 (p q : Pattern) (h : Agree support p q) : d3391 p = d3391 q := by
  simp only [d3391, h 224 (by decide), agree3358 p q h, agree3390 p q h]
theorem nonnegative3391 (p : Pattern) : 0 ≤ d3391 p :=
  nonnegative_ite (p 224) (nonnegative3358 p) (nonnegative3390 p)
def d3392 (p : Pattern) : Int := if p 204 then d3358 p else d3391 p
theorem agree3392 (p q : Pattern) (h : Agree support p q) : d3392 p = d3392 q := by
  simp only [d3392, h 204 (by decide), agree3358 p q h, agree3391 p q h]
theorem nonnegative3392 (p : Pattern) : 0 ≤ d3392 p :=
  nonnegative_ite (p 204) (nonnegative3358 p) (nonnegative3391 p)
def d3393 (p : Pattern) : Int := if p 182 then d3362 p else d3392 p
theorem agree3393 (p q : Pattern) (h : Agree support p q) : d3393 p = d3393 q := by
  simp only [d3393, h 182 (by decide), agree3362 p q h, agree3392 p q h]
theorem nonnegative3393 (p : Pattern) : 0 ≤ d3393 p :=
  nonnegative_ite (p 182) (nonnegative3362 p) (nonnegative3392 p)
def d3394 (p : Pattern) : Int := if p 182 then d3375 p else d3374 p
theorem agree3394 (p q : Pattern) (h : Agree support p q) : d3394 p = d3394 q := by
  simp only [d3394, h 182 (by decide), agree3375 p q h, agree3374 p q h]
theorem nonnegative3394 (p : Pattern) : 0 ≤ d3394 p :=
  nonnegative_ite (p 182) (nonnegative3375 p) (nonnegative3374 p)
def d3395 (p : Pattern) : Int := if p 163 then d3394 p else d3393 p
theorem agree3395 (p q : Pattern) (h : Agree support p q) : d3395 p = d3395 q := by
  simp only [d3395, h 163 (by decide), agree3394 p q h, agree3393 p q h]
theorem nonnegative3395 (p : Pattern) : 0 ≤ d3395 p :=
  nonnegative_ite (p 163) (nonnegative3394 p) (nonnegative3393 p)
def d3396 (p : Pattern) : Int := if p 163 then d3281 p else d3368 p
theorem agree3396 (p q : Pattern) (h : Agree support p q) : d3396 p = d3396 q := by
  simp only [d3396, h 163 (by decide), agree3281 p q h, agree3368 p q h]
theorem nonnegative3396 (p : Pattern) : 0 ≤ d3396 p :=
  nonnegative_ite (p 163) (nonnegative3281 p) (nonnegative3368 p)
def d3397 (p : Pattern) : Int := if p 162 then d3396 p else d3395 p
theorem agree3397 (p q : Pattern) (h : Agree support p q) : d3397 p = d3397 q := by
  simp only [d3397, h 162 (by decide), agree3396 p q h, agree3395 p q h]
theorem nonnegative3397 (p : Pattern) : 0 ≤ d3397 p :=
  nonnegative_ite (p 162) (nonnegative3396 p) (nonnegative3395 p)
def d3398 (p : Pattern) : Int := if p 163 then d3283 p else d3368 p
theorem agree3398 (p q : Pattern) (h : Agree support p q) : d3398 p = d3398 q := by
  simp only [d3398, h 163 (by decide), agree3283 p q h, agree3368 p q h]
theorem nonnegative3398 (p : Pattern) : 0 ≤ d3398 p :=
  nonnegative_ite (p 163) (nonnegative3283 p) (nonnegative3368 p)
def d3399 (p : Pattern) : Int := if p 162 then d12 p else d3398 p
theorem agree3399 (p q : Pattern) (h : Agree support p q) : d3399 p = d3399 q := by
  simp only [d3399, h 162 (by decide), agree12 p q h, agree3398 p q h]
theorem nonnegative3399 (p : Pattern) : 0 ≤ d3399 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3398 p)
def d3400 (p : Pattern) : Int := if p 161 then d3399 p else d3397 p
theorem agree3400 (p q : Pattern) (h : Agree support p q) : d3400 p = d3400 q := by
  simp only [d3400, h 161 (by decide), agree3399 p q h, agree3397 p q h]
theorem nonnegative3400 (p : Pattern) : 0 ≤ d3400 p :=
  nonnegative_ite (p 161) (nonnegative3399 p) (nonnegative3397 p)
def d3401 (p : Pattern) : Int := if p 182 then d12 p else d3374 p
theorem agree3401 (p q : Pattern) (h : Agree support p q) : d3401 p = d3401 q := by
  simp only [d3401, h 182 (by decide), agree12 p q h, agree3374 p q h]
theorem nonnegative3401 (p : Pattern) : 0 ≤ d3401 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3374 p)
def d3402 (p : Pattern) : Int := if p 163 then d3401 p else d3379 p
theorem agree3402 (p q : Pattern) (h : Agree support p q) : d3402 p = d3402 q := by
  simp only [d3402, h 163 (by decide), agree3401 p q h, agree3379 p q h]
theorem nonnegative3402 (p : Pattern) : 0 ≤ d3402 p :=
  nonnegative_ite (p 163) (nonnegative3401 p) (nonnegative3379 p)
def d3403 (p : Pattern) : Int := if p 163 then d3291 p else d3382 p
theorem agree3403 (p q : Pattern) (h : Agree support p q) : d3403 p = d3403 q := by
  simp only [d3403, h 163 (by decide), agree3291 p q h, agree3382 p q h]
theorem nonnegative3403 (p : Pattern) : 0 ≤ d3403 p :=
  nonnegative_ite (p 163) (nonnegative3291 p) (nonnegative3382 p)
def d3404 (p : Pattern) : Int := if p 162 then d3403 p else d3402 p
theorem agree3404 (p q : Pattern) (h : Agree support p q) : d3404 p = d3404 q := by
  simp only [d3404, h 162 (by decide), agree3403 p q h, agree3402 p q h]
theorem nonnegative3404 (p : Pattern) : 0 ≤ d3404 p :=
  nonnegative_ite (p 162) (nonnegative3403 p) (nonnegative3402 p)
def d3405 (p : Pattern) : Int := if p 163 then d3293 p else d3382 p
theorem agree3405 (p q : Pattern) (h : Agree support p q) : d3405 p = d3405 q := by
  simp only [d3405, h 163 (by decide), agree3293 p q h, agree3382 p q h]
theorem nonnegative3405 (p : Pattern) : 0 ≤ d3405 p :=
  nonnegative_ite (p 163) (nonnegative3293 p) (nonnegative3382 p)
def d3406 (p : Pattern) : Int := if p 162 then d12 p else d3405 p
theorem agree3406 (p q : Pattern) (h : Agree support p q) : d3406 p = d3406 q := by
  simp only [d3406, h 162 (by decide), agree12 p q h, agree3405 p q h]
theorem nonnegative3406 (p : Pattern) : 0 ≤ d3406 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3405 p)
def d3407 (p : Pattern) : Int := if p 161 then d3406 p else d3404 p
theorem agree3407 (p q : Pattern) (h : Agree support p q) : d3407 p = d3407 q := by
  simp only [d3407, h 161 (by decide), agree3406 p q h, agree3404 p q h]
theorem nonnegative3407 (p : Pattern) : 0 ≤ d3407 p :=
  nonnegative_ite (p 161) (nonnegative3406 p) (nonnegative3404 p)
def d3408 (p : Pattern) : Int := if p 160 then d3407 p else d3400 p
theorem agree3408 (p q : Pattern) (h : Agree support p q) : d3408 p = d3408 q := by
  simp only [d3408, h 160 (by decide), agree3407 p q h, agree3400 p q h]
theorem nonnegative3408 (p : Pattern) : 0 ≤ d3408 p :=
  nonnegative_ite (p 160) (nonnegative3407 p) (nonnegative3400 p)
def d3409 (p : Pattern) : Int := if p 141 then d3408 p else d3388 p
theorem agree3409 (p q : Pattern) (h : Agree support p q) : d3409 p = d3409 q := by
  simp only [d3409, h 141 (by decide), agree3408 p q h, agree3388 p q h]
theorem nonnegative3409 (p : Pattern) : 0 ≤ d3409 p :=
  nonnegative_ite (p 141) (nonnegative3408 p) (nonnegative3388 p)
def d3410 (p : Pattern) : Int := if p 162 then d3369 p else d3364 p
theorem agree3410 (p q : Pattern) (h : Agree support p q) : d3410 p = d3410 q := by
  simp only [d3410, h 162 (by decide), agree3369 p q h, agree3364 p q h]
theorem nonnegative3410 (p : Pattern) : 0 ≤ d3410 p :=
  nonnegative_ite (p 162) (nonnegative3369 p) (nonnegative3364 p)
def d3411 (p : Pattern) : Int := if p 161 then d3372 p else d3410 p
theorem agree3411 (p q : Pattern) (h : Agree support p q) : d3411 p = d3411 q := by
  simp only [d3411, h 161 (by decide), agree3372 p q h, agree3410 p q h]
theorem nonnegative3411 (p : Pattern) : 0 ≤ d3411 p :=
  nonnegative_ite (p 161) (nonnegative3372 p) (nonnegative3410 p)
def d3412 (p : Pattern) : Int := if p 182 then d3378 p else d3377 p
theorem agree3412 (p q : Pattern) (h : Agree support p q) : d3412 p = d3412 q := by
  simp only [d3412, h 182 (by decide), agree3378 p q h, agree3377 p q h]
theorem nonnegative3412 (p : Pattern) : 0 ≤ d3412 p :=
  nonnegative_ite (p 182) (nonnegative3378 p) (nonnegative3377 p)
def d3413 (p : Pattern) : Int := if p 163 then d3412 p else d3394 p
theorem agree3413 (p q : Pattern) (h : Agree support p q) : d3413 p = d3413 q := by
  simp only [d3413, h 163 (by decide), agree3412 p q h, agree3394 p q h]
theorem nonnegative3413 (p : Pattern) : 0 ≤ d3413 p :=
  nonnegative_ite (p 163) (nonnegative3412 p) (nonnegative3394 p)
def d3414 (p : Pattern) : Int := if p 162 then d12 p else d3413 p
theorem agree3414 (p q : Pattern) (h : Agree support p q) : d3414 p = d3414 q := by
  simp only [d3414, h 162 (by decide), agree12 p q h, agree3413 p q h]
theorem nonnegative3414 (p : Pattern) : 0 ≤ d3414 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3413 p)
def d3415 (p : Pattern) : Int := if p 161 then d12 p else d3414 p
theorem agree3415 (p q : Pattern) (h : Agree support p q) : d3415 p = d3415 q := by
  simp only [d3415, h 161 (by decide), agree12 p q h, agree3414 p q h]
theorem nonnegative3415 (p : Pattern) : 0 ≤ d3415 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3414 p)
def d3416 (p : Pattern) : Int := if p 160 then d3415 p else d3411 p
theorem agree3416 (p q : Pattern) (h : Agree support p q) : d3416 p = d3416 q := by
  simp only [d3416, h 160 (by decide), agree3415 p q h, agree3411 p q h]
theorem nonnegative3416 (p : Pattern) : 0 ≤ d3416 p :=
  nonnegative_ite (p 160) (nonnegative3415 p) (nonnegative3411 p)
def d3417 (p : Pattern) : Int := if p 163 then d3394 p else d3364 p
theorem agree3417 (p q : Pattern) (h : Agree support p q) : d3417 p = d3417 q := by
  simp only [d3417, h 163 (by decide), agree3394 p q h, agree3364 p q h]
theorem nonnegative3417 (p : Pattern) : 0 ≤ d3417 p :=
  nonnegative_ite (p 163) (nonnegative3394 p) (nonnegative3364 p)
def d3418 (p : Pattern) : Int := if p 162 then d3396 p else d3417 p
theorem agree3418 (p q : Pattern) (h : Agree support p q) : d3418 p = d3418 q := by
  simp only [d3418, h 162 (by decide), agree3396 p q h, agree3417 p q h]
theorem nonnegative3418 (p : Pattern) : 0 ≤ d3418 p :=
  nonnegative_ite (p 162) (nonnegative3396 p) (nonnegative3417 p)
def d3419 (p : Pattern) : Int := if p 161 then d3399 p else d3418 p
theorem agree3419 (p q : Pattern) (h : Agree support p q) : d3419 p = d3419 q := by
  simp only [d3419, h 161 (by decide), agree3399 p q h, agree3418 p q h]
theorem nonnegative3419 (p : Pattern) : 0 ≤ d3419 p :=
  nonnegative_ite (p 161) (nonnegative3399 p) (nonnegative3418 p)
def d3420 (p : Pattern) : Int := if p 163 then d12 p else d3412 p
theorem agree3420 (p q : Pattern) (h : Agree support p q) : d3420 p = d3420 q := by
  simp only [d3420, h 163 (by decide), agree12 p q h, agree3412 p q h]
theorem nonnegative3420 (p : Pattern) : 0 ≤ d3420 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3412 p)
def d3421 (p : Pattern) : Int := if p 162 then d12 p else d3420 p
theorem agree3421 (p q : Pattern) (h : Agree support p q) : d3421 p = d3421 q := by
  simp only [d3421, h 162 (by decide), agree12 p q h, agree3420 p q h]
theorem nonnegative3421 (p : Pattern) : 0 ≤ d3421 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3420 p)
def d3422 (p : Pattern) : Int := if p 161 then d12 p else d3421 p
theorem agree3422 (p q : Pattern) (h : Agree support p q) : d3422 p = d3422 q := by
  simp only [d3422, h 161 (by decide), agree12 p q h, agree3421 p q h]
theorem nonnegative3422 (p : Pattern) : 0 ≤ d3422 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3421 p)
def d3423 (p : Pattern) : Int := if p 160 then d3422 p else d3419 p
theorem agree3423 (p q : Pattern) (h : Agree support p q) : d3423 p = d3423 q := by
  simp only [d3423, h 160 (by decide), agree3422 p q h, agree3419 p q h]
theorem nonnegative3423 (p : Pattern) : 0 ≤ d3423 p :=
  nonnegative_ite (p 160) (nonnegative3422 p) (nonnegative3419 p)
def d3424 (p : Pattern) : Int := if p 141 then d3423 p else d3416 p
theorem agree3424 (p q : Pattern) (h : Agree support p q) : d3424 p = d3424 q := by
  simp only [d3424, h 141 (by decide), agree3423 p q h, agree3416 p q h]
theorem nonnegative3424 (p : Pattern) : 0 ≤ d3424 p :=
  nonnegative_ite (p 141) (nonnegative3423 p) (nonnegative3416 p)
def d3425 (p : Pattern) : Int := if p 138 then d3424 p else d3409 p
theorem agree3425 (p q : Pattern) (h : Agree support p q) : d3425 p = d3425 q := by
  simp only [d3425, h 138 (by decide), agree3424 p q h, agree3409 p q h]
theorem nonnegative3425 (p : Pattern) : 0 ≤ d3425 p :=
  nonnegative_ite (p 138) (nonnegative3424 p) (nonnegative3409 p)
def d3426 (p : Pattern) : Int := if p 162 then d12 p else d3371 p
theorem agree3426 (p q : Pattern) (h : Agree support p q) : d3426 p = d3426 q := by
  simp only [d3426, h 162 (by decide), agree12 p q h, agree3371 p q h]
theorem nonnegative3426 (p : Pattern) : 0 ≤ d3426 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3371 p)
def d3427 (p : Pattern) : Int := if p 161 then d12 p else d3426 p
theorem agree3427 (p q : Pattern) (h : Agree support p q) : d3427 p = d3427 q := by
  simp only [d3427, h 161 (by decide), agree12 p q h, agree3426 p q h]
theorem nonnegative3427 (p : Pattern) : 0 ≤ d3427 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3426 p)
def d3428 (p : Pattern) : Int := if p 160 then d12 p else d3427 p
theorem agree3428 (p q : Pattern) (h : Agree support p q) : d3428 p = d3428 q := by
  simp only [d3428, h 160 (by decide), agree12 p q h, agree3427 p q h]
theorem nonnegative3428 (p : Pattern) : 0 ≤ d3428 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative3427 p)
def d3429 (p : Pattern) : Int := if p 141 then d12 p else d3428 p
theorem agree3429 (p q : Pattern) (h : Agree support p q) : d3429 p = d3429 q := by
  simp only [d3429, h 141 (by decide), agree12 p q h, agree3428 p q h]
theorem nonnegative3429 (p : Pattern) : 0 ≤ d3429 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative3428 p)
def d3430 (p : Pattern) : Int := if p 138 then d3429 p else d3424 p
theorem agree3430 (p q : Pattern) (h : Agree support p q) : d3430 p = d3430 q := by
  simp only [d3430, h 138 (by decide), agree3429 p q h, agree3424 p q h]
theorem nonnegative3430 (p : Pattern) : 0 ≤ d3430 p :=
  nonnegative_ite (p 138) (nonnegative3429 p) (nonnegative3424 p)
def d3431 (p : Pattern) : Int := if p 116 then d3430 p else d3425 p
theorem agree3431 (p q : Pattern) (h : Agree support p q) : d3431 p = d3431 q := by
  simp only [d3431, h 116 (by decide), agree3430 p q h, agree3425 p q h]
theorem nonnegative3431 (p : Pattern) : 0 ≤ d3431 p :=
  nonnegative_ite (p 116) (nonnegative3430 p) (nonnegative3425 p)
def d3432 (p : Pattern) : Int := if p 160 then d3387 p else d3411 p
theorem agree3432 (p q : Pattern) (h : Agree support p q) : d3432 p = d3432 q := by
  simp only [d3432, h 160 (by decide), agree3387 p q h, agree3411 p q h]
theorem nonnegative3432 (p : Pattern) : 0 ≤ d3432 p :=
  nonnegative_ite (p 160) (nonnegative3387 p) (nonnegative3411 p)
def d3433 (p : Pattern) : Int := if p 160 then d3407 p else d3419 p
theorem agree3433 (p q : Pattern) (h : Agree support p q) : d3433 p = d3433 q := by
  simp only [d3433, h 160 (by decide), agree3407 p q h, agree3419 p q h]
theorem nonnegative3433 (p : Pattern) : 0 ≤ d3433 p :=
  nonnegative_ite (p 160) (nonnegative3407 p) (nonnegative3419 p)
def d3434 (p : Pattern) : Int := if p 141 then d3433 p else d3432 p
theorem agree3434 (p q : Pattern) (h : Agree support p q) : d3434 p = d3434 q := by
  simp only [d3434, h 141 (by decide), agree3433 p q h, agree3432 p q h]
theorem nonnegative3434 (p : Pattern) : 0 ≤ d3434 p :=
  nonnegative_ite (p 141) (nonnegative3433 p) (nonnegative3432 p)
def d3435 (p : Pattern) : Int := if p 138 then d3424 p else d3434 p
theorem agree3435 (p q : Pattern) (h : Agree support p q) : d3435 p = d3435 q := by
  simp only [d3435, h 138 (by decide), agree3424 p q h, agree3434 p q h]
theorem nonnegative3435 (p : Pattern) : 0 ≤ d3435 p :=
  nonnegative_ite (p 138) (nonnegative3424 p) (nonnegative3434 p)
def d3436 (p : Pattern) : Int := if p 138 then d12 p else d3424 p
theorem agree3436 (p q : Pattern) (h : Agree support p q) : d3436 p = d3436 q := by
  simp only [d3436, h 138 (by decide), agree12 p q h, agree3424 p q h]
theorem nonnegative3436 (p : Pattern) : 0 ≤ d3436 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative3424 p)
def d3437 (p : Pattern) : Int := if p 116 then d3436 p else d3435 p
theorem agree3437 (p q : Pattern) (h : Agree support p q) : d3437 p = d3437 q := by
  simp only [d3437, h 116 (by decide), agree3436 p q h, agree3435 p q h]
theorem nonnegative3437 (p : Pattern) : 0 ≤ d3437 p :=
  nonnegative_ite (p 116) (nonnegative3436 p) (nonnegative3435 p)
def d3438 (p : Pattern) : Int := if p 115 then d3437 p else d3431 p
theorem agree3438 (p q : Pattern) (h : Agree support p q) : d3438 p = d3438 q := by
  simp only [d3438, h 115 (by decide), agree3437 p q h, agree3431 p q h]
theorem nonnegative3438 (p : Pattern) : 0 ≤ d3438 p :=
  nonnegative_ite (p 115) (nonnegative3437 p) (nonnegative3431 p)
def d3439 (p : Pattern) : Int := if p 71 then d3438 p else d3334 p
theorem agree3439 (p q : Pattern) (h : Agree support p q) : d3439 p = d3439 q := by
  simp only [d3439, h 71 (by decide), agree3438 p q h, agree3334 p q h]
theorem nonnegative3439 (p : Pattern) : 0 ≤ d3439 p :=
  nonnegative_ite (p 71) (nonnegative3438 p) (nonnegative3334 p)
def d3440 (p : Pattern) : Int := if p 49 then d3439 p else d3356 p
theorem agree3440 (p q : Pattern) (h : Agree support p q) : d3440 p = d3440 q := by
  simp only [d3440, h 49 (by decide), agree3439 p q h, agree3356 p q h]
theorem nonnegative3440 (p : Pattern) : 0 ≤ d3440 p :=
  nonnegative_ite (p 49) (nonnegative3439 p) (nonnegative3356 p)
def d3441 (p : Pattern) : Int := if p 182 then d3254 p else d3250 p
theorem agree3441 (p q : Pattern) (h : Agree support p q) : d3441 p = d3441 q := by
  simp only [d3441, h 182 (by decide), agree3254 p q h, agree3250 p q h]
theorem nonnegative3441 (p : Pattern) : 0 ≤ d3441 p :=
  nonnegative_ite (p 182) (nonnegative3254 p) (nonnegative3250 p)
def d3442 (p : Pattern) : Int := if p 163 then d3441 p else d3275 p
theorem agree3442 (p q : Pattern) (h : Agree support p q) : d3442 p = d3442 q := by
  simp only [d3442, h 163 (by decide), agree3441 p q h, agree3275 p q h]
theorem nonnegative3442 (p : Pattern) : 0 ≤ d3442 p :=
  nonnegative_ite (p 163) (nonnegative3441 p) (nonnegative3275 p)
def d3443 (p : Pattern) : Int := if p 182 then d3258 p else d3250 p
theorem agree3443 (p q : Pattern) (h : Agree support p q) : d3443 p = d3443 q := by
  simp only [d3443, h 182 (by decide), agree3258 p q h, agree3250 p q h]
theorem nonnegative3443 (p : Pattern) : 0 ≤ d3443 p :=
  nonnegative_ite (p 182) (nonnegative3258 p) (nonnegative3250 p)
def d3444 (p : Pattern) : Int := if p 182 then d12 p else d3253 p
theorem agree3444 (p q : Pattern) (h : Agree support p q) : d3444 p = d3444 q := by
  simp only [d3444, h 182 (by decide), agree12 p q h, agree3253 p q h]
theorem nonnegative3444 (p : Pattern) : 0 ≤ d3444 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3253 p)
def d3445 (p : Pattern) : Int := if p 163 then d3444 p else d3443 p
theorem agree3445 (p q : Pattern) (h : Agree support p q) : d3445 p = d3445 q := by
  simp only [d3445, h 163 (by decide), agree3444 p q h, agree3443 p q h]
theorem nonnegative3445 (p : Pattern) : 0 ≤ d3445 p :=
  nonnegative_ite (p 163) (nonnegative3444 p) (nonnegative3443 p)
def d3446 (p : Pattern) : Int := if p 162 then d3445 p else d3442 p
theorem agree3446 (p q : Pattern) (h : Agree support p q) : d3446 p = d3446 q := by
  simp only [d3446, h 162 (by decide), agree3445 p q h, agree3442 p q h]
theorem nonnegative3446 (p : Pattern) : 0 ≤ d3446 p :=
  nonnegative_ite (p 162) (nonnegative3445 p) (nonnegative3442 p)
def d3447 (p : Pattern) : Int := if p 163 then d3444 p else d3287 p
theorem agree3447 (p q : Pattern) (h : Agree support p q) : d3447 p = d3447 q := by
  simp only [d3447, h 163 (by decide), agree3444 p q h, agree3287 p q h]
theorem nonnegative3447 (p : Pattern) : 0 ≤ d3447 p :=
  nonnegative_ite (p 163) (nonnegative3444 p) (nonnegative3287 p)
def d3448 (p : Pattern) : Int := if p 162 then d3294 p else d3447 p
theorem agree3448 (p q : Pattern) (h : Agree support p q) : d3448 p = d3448 q := by
  simp only [d3448, h 162 (by decide), agree3294 p q h, agree3447 p q h]
theorem nonnegative3448 (p : Pattern) : 0 ≤ d3448 p :=
  nonnegative_ite (p 162) (nonnegative3294 p) (nonnegative3447 p)
def d3449 (p : Pattern) : Int := if p 161 then d3448 p else d3446 p
theorem agree3449 (p q : Pattern) (h : Agree support p q) : d3449 p = d3449 q := by
  simp only [d3449, h 161 (by decide), agree3448 p q h, agree3446 p q h]
theorem nonnegative3449 (p : Pattern) : 0 ≤ d3449 p :=
  nonnegative_ite (p 161) (nonnegative3448 p) (nonnegative3446 p)
def d3450 (p : Pattern) : Int := if p 160 then d3449 p else d3300 p
theorem agree3450 (p q : Pattern) (h : Agree support p q) : d3450 p = d3450 q := by
  simp only [d3450, h 160 (by decide), agree3449 p q h, agree3300 p q h]
theorem nonnegative3450 (p : Pattern) : 0 ≤ d3450 p :=
  nonnegative_ite (p 160) (nonnegative3449 p) (nonnegative3300 p)
def d3451 (p : Pattern) : Int := if p 163 then d3260 p else d3441 p
theorem agree3451 (p q : Pattern) (h : Agree support p q) : d3451 p = d3451 q := by
  simp only [d3451, h 163 (by decide), agree3260 p q h, agree3441 p q h]
theorem nonnegative3451 (p : Pattern) : 0 ≤ d3451 p :=
  nonnegative_ite (p 163) (nonnegative3260 p) (nonnegative3441 p)
def d3452 (p : Pattern) : Int := if p 163 then d3293 p else d3444 p
theorem agree3452 (p q : Pattern) (h : Agree support p q) : d3452 p = d3452 q := by
  simp only [d3452, h 163 (by decide), agree3293 p q h, agree3444 p q h]
theorem nonnegative3452 (p : Pattern) : 0 ≤ d3452 p :=
  nonnegative_ite (p 163) (nonnegative3293 p) (nonnegative3444 p)
def d3453 (p : Pattern) : Int := if p 162 then d3452 p else d3451 p
theorem agree3453 (p q : Pattern) (h : Agree support p q) : d3453 p = d3453 q := by
  simp only [d3453, h 162 (by decide), agree3452 p q h, agree3451 p q h]
theorem nonnegative3453 (p : Pattern) : 0 ≤ d3453 p :=
  nonnegative_ite (p 162) (nonnegative3452 p) (nonnegative3451 p)
def d3454 (p : Pattern) : Int := if p 163 then d12 p else d3444 p
theorem agree3454 (p q : Pattern) (h : Agree support p q) : d3454 p = d3454 q := by
  simp only [d3454, h 163 (by decide), agree12 p q h, agree3444 p q h]
theorem nonnegative3454 (p : Pattern) : 0 ≤ d3454 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3444 p)
def d3455 (p : Pattern) : Int := if p 162 then d12 p else d3454 p
theorem agree3455 (p q : Pattern) (h : Agree support p q) : d3455 p = d3455 q := by
  simp only [d3455, h 162 (by decide), agree12 p q h, agree3454 p q h]
theorem nonnegative3455 (p : Pattern) : 0 ≤ d3455 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3454 p)
def d3456 (p : Pattern) : Int := if p 161 then d3455 p else d3453 p
theorem agree3456 (p q : Pattern) (h : Agree support p q) : d3456 p = d3456 q := by
  simp only [d3456, h 161 (by decide), agree3455 p q h, agree3453 p q h]
theorem nonnegative3456 (p : Pattern) : 0 ≤ d3456 p :=
  nonnegative_ite (p 161) (nonnegative3455 p) (nonnegative3453 p)
def d3457 (p : Pattern) : Int := if p 160 then d3456 p else d3308 p
theorem agree3457 (p q : Pattern) (h : Agree support p q) : d3457 p = d3457 q := by
  simp only [d3457, h 160 (by decide), agree3456 p q h, agree3308 p q h]
theorem nonnegative3457 (p : Pattern) : 0 ≤ d3457 p :=
  nonnegative_ite (p 160) (nonnegative3456 p) (nonnegative3308 p)
def d3458 (p : Pattern) : Int := if p 141 then d3457 p else d3450 p
theorem agree3458 (p q : Pattern) (h : Agree support p q) : d3458 p = d3458 q := by
  simp only [d3458, h 141 (by decide), agree3457 p q h, agree3450 p q h]
theorem nonnegative3458 (p : Pattern) : 0 ≤ d3458 p :=
  nonnegative_ite (p 141) (nonnegative3457 p) (nonnegative3450 p)
def d3459 (p : Pattern) : Int := if p 162 then d3302 p else d3238 p
theorem agree3459 (p q : Pattern) (h : Agree support p q) : d3459 p = d3459 q := by
  simp only [d3459, h 162 (by decide), agree3302 p q h, agree3238 p q h]
theorem nonnegative3459 (p : Pattern) : 0 ≤ d3459 p :=
  nonnegative_ite (p 162) (nonnegative3302 p) (nonnegative3238 p)
def d3460 (p : Pattern) : Int := if p 161 then d3303 p else d3459 p
theorem agree3460 (p q : Pattern) (h : Agree support p q) : d3460 p = d3460 q := by
  simp only [d3460, h 161 (by decide), agree3303 p q h, agree3459 p q h]
theorem nonnegative3460 (p : Pattern) : 0 ≤ d3460 p :=
  nonnegative_ite (p 161) (nonnegative3303 p) (nonnegative3459 p)
def d3461 (p : Pattern) : Int := if p 246 then d12 p else d8 p
theorem agree3461 (p q : Pattern) (h : Agree support p q) : d3461 p = d3461 q := by
  simp only [d3461, h 246 (by decide), agree12 p q h, agree8 p q h]
theorem nonnegative3461 (p : Pattern) : 0 ≤ d3461 p :=
  nonnegative_ite (p 246) (nonnegative12 p) (nonnegative8 p)
def d3462 (p : Pattern) : Int := if p 204 then d12 p else d3461 p
theorem agree3462 (p q : Pattern) (h : Agree support p q) : d3462 p = d3462 q := by
  simp only [d3462, h 204 (by decide), agree12 p q h, agree3461 p q h]
theorem nonnegative3462 (p : Pattern) : 0 ≤ d3462 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3461 p)
def d3463 (p : Pattern) : Int := if p 182 then d3462 p else d3461 p
theorem agree3463 (p q : Pattern) (h : Agree support p q) : d3463 p = d3463 q := by
  simp only [d3463, h 182 (by decide), agree3462 p q h, agree3461 p q h]
theorem nonnegative3463 (p : Pattern) : 0 ≤ d3463 p :=
  nonnegative_ite (p 182) (nonnegative3462 p) (nonnegative3461 p)
def d3464 (p : Pattern) : Int := if p 163 then d3463 p else d3241 p
theorem agree3464 (p q : Pattern) (h : Agree support p q) : d3464 p = d3464 q := by
  simp only [d3464, h 163 (by decide), agree3463 p q h, agree3241 p q h]
theorem nonnegative3464 (p : Pattern) : 0 ≤ d3464 p :=
  nonnegative_ite (p 163) (nonnegative3463 p) (nonnegative3241 p)
def d3465 (p : Pattern) : Int := if p 162 then d12 p else d3464 p
theorem agree3465 (p q : Pattern) (h : Agree support p q) : d3465 p = d3465 q := by
  simp only [d3465, h 162 (by decide), agree12 p q h, agree3464 p q h]
theorem nonnegative3465 (p : Pattern) : 0 ≤ d3465 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3464 p)
def d3466 (p : Pattern) : Int := if p 161 then d12 p else d3465 p
theorem agree3466 (p q : Pattern) (h : Agree support p q) : d3466 p = d3466 q := by
  simp only [d3466, h 161 (by decide), agree12 p q h, agree3465 p q h]
theorem nonnegative3466 (p : Pattern) : 0 ≤ d3466 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3465 p)
def d3467 (p : Pattern) : Int := if p 160 then d3466 p else d3460 p
theorem agree3467 (p q : Pattern) (h : Agree support p q) : d3467 p = d3467 q := by
  simp only [d3467, h 160 (by decide), agree3466 p q h, agree3460 p q h]
theorem nonnegative3467 (p : Pattern) : 0 ≤ d3467 p :=
  nonnegative_ite (p 160) (nonnegative3466 p) (nonnegative3460 p)
def d3468 (p : Pattern) : Int := if p 163 then d3283 p else d3241 p
theorem agree3468 (p q : Pattern) (h : Agree support p q) : d3468 p = d3468 q := by
  simp only [d3468, h 163 (by decide), agree3283 p q h, agree3241 p q h]
theorem nonnegative3468 (p : Pattern) : 0 ≤ d3468 p :=
  nonnegative_ite (p 163) (nonnegative3283 p) (nonnegative3241 p)
def d3469 (p : Pattern) : Int := if p 162 then d3468 p else d3275 p
theorem agree3469 (p q : Pattern) (h : Agree support p q) : d3469 p = d3469 q := by
  simp only [d3469, h 162 (by decide), agree3468 p q h, agree3275 p q h]
theorem nonnegative3469 (p : Pattern) : 0 ≤ d3469 p :=
  nonnegative_ite (p 162) (nonnegative3468 p) (nonnegative3275 p)
def d3470 (p : Pattern) : Int := if p 161 then d3310 p else d3469 p
theorem agree3470 (p q : Pattern) (h : Agree support p q) : d3470 p = d3470 q := by
  simp only [d3470, h 161 (by decide), agree3310 p q h, agree3469 p q h]
theorem nonnegative3470 (p : Pattern) : 0 ≤ d3470 p :=
  nonnegative_ite (p 161) (nonnegative3310 p) (nonnegative3469 p)
def d3471 (p : Pattern) : Int := if p 163 then d12 p else d3463 p
theorem agree3471 (p q : Pattern) (h : Agree support p q) : d3471 p = d3471 q := by
  simp only [d3471, h 163 (by decide), agree12 p q h, agree3463 p q h]
theorem nonnegative3471 (p : Pattern) : 0 ≤ d3471 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3463 p)
def d3472 (p : Pattern) : Int := if p 162 then d12 p else d3471 p
theorem agree3472 (p q : Pattern) (h : Agree support p q) : d3472 p = d3472 q := by
  simp only [d3472, h 162 (by decide), agree12 p q h, agree3471 p q h]
theorem nonnegative3472 (p : Pattern) : 0 ≤ d3472 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3471 p)
def d3473 (p : Pattern) : Int := if p 161 then d12 p else d3472 p
theorem agree3473 (p q : Pattern) (h : Agree support p q) : d3473 p = d3473 q := by
  simp only [d3473, h 161 (by decide), agree12 p q h, agree3472 p q h]
theorem nonnegative3473 (p : Pattern) : 0 ≤ d3473 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3472 p)
def d3474 (p : Pattern) : Int := if p 160 then d3473 p else d3470 p
theorem agree3474 (p q : Pattern) (h : Agree support p q) : d3474 p = d3474 q := by
  simp only [d3474, h 160 (by decide), agree3473 p q h, agree3470 p q h]
theorem nonnegative3474 (p : Pattern) : 0 ≤ d3474 p :=
  nonnegative_ite (p 160) (nonnegative3473 p) (nonnegative3470 p)
def d3475 (p : Pattern) : Int := if p 141 then d3474 p else d3467 p
theorem agree3475 (p q : Pattern) (h : Agree support p q) : d3475 p = d3475 q := by
  simp only [d3475, h 141 (by decide), agree3474 p q h, agree3467 p q h]
theorem nonnegative3475 (p : Pattern) : 0 ≤ d3475 p :=
  nonnegative_ite (p 141) (nonnegative3474 p) (nonnegative3467 p)
def d3476 (p : Pattern) : Int := if p 138 then d3475 p else d3458 p
theorem agree3476 (p q : Pattern) (h : Agree support p q) : d3476 p = d3476 q := by
  simp only [d3476, h 138 (by decide), agree3475 p q h, agree3458 p q h]
theorem nonnegative3476 (p : Pattern) : 0 ≤ d3476 p :=
  nonnegative_ite (p 138) (nonnegative3475 p) (nonnegative3458 p)
def d3477 (p : Pattern) : Int := if p 138 then d12 p else d3475 p
theorem agree3477 (p q : Pattern) (h : Agree support p q) : d3477 p = d3477 q := by
  simp only [d3477, h 138 (by decide), agree12 p q h, agree3475 p q h]
theorem nonnegative3477 (p : Pattern) : 0 ≤ d3477 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative3475 p)
def d3478 (p : Pattern) : Int := if p 116 then d3477 p else d3476 p
theorem agree3478 (p q : Pattern) (h : Agree support p q) : d3478 p = d3478 q := by
  simp only [d3478, h 116 (by decide), agree3477 p q h, agree3476 p q h]
theorem nonnegative3478 (p : Pattern) : 0 ≤ d3478 p :=
  nonnegative_ite (p 116) (nonnegative3477 p) (nonnegative3476 p)
def d3479 (p : Pattern) : Int := if p 115 then d3478 p else d3350 p
theorem agree3479 (p q : Pattern) (h : Agree support p q) : d3479 p = d3479 q := by
  simp only [d3479, h 115 (by decide), agree3478 p q h, agree3350 p q h]
theorem nonnegative3479 (p : Pattern) : 0 ≤ d3479 p :=
  nonnegative_ite (p 115) (nonnegative3478 p) (nonnegative3350 p)
end NetHack.Sokoban22Refined85
