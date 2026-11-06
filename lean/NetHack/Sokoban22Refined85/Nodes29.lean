/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes28
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d3480 (p : Pattern) : Int := if p 71 then d3479 p else d3334 p
theorem agree3480 (p q : Pattern) (h : Agree support p q) : d3480 p = d3480 q := by
  simp only [d3480, h 71 (by decide), agree3479 p q h, agree3334 p q h]
theorem nonnegative3480 (p : Pattern) : 0 ≤ d3480 p :=
  nonnegative_ite (p 71) (nonnegative3479 p) (nonnegative3334 p)
def d3481 (p : Pattern) : Int := if p 163 then d12 p else d3368 p
theorem agree3481 (p q : Pattern) (h : Agree support p q) : d3481 p = d3481 q := by
  simp only [d3481, h 163 (by decide), agree12 p q h, agree3368 p q h]
theorem nonnegative3481 (p : Pattern) : 0 ≤ d3481 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3368 p)
def d3482 (p : Pattern) : Int := if p 162 then d3481 p else d3395 p
theorem agree3482 (p q : Pattern) (h : Agree support p q) : d3482 p = d3482 q := by
  simp only [d3482, h 162 (by decide), agree3481 p q h, agree3395 p q h]
theorem nonnegative3482 (p : Pattern) : 0 ≤ d3482 p :=
  nonnegative_ite (p 162) (nonnegative3481 p) (nonnegative3395 p)
def d3483 (p : Pattern) : Int := if p 162 then d12 p else d3481 p
theorem agree3483 (p q : Pattern) (h : Agree support p q) : d3483 p = d3483 q := by
  simp only [d3483, h 162 (by decide), agree12 p q h, agree3481 p q h]
theorem nonnegative3483 (p : Pattern) : 0 ≤ d3483 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3481 p)
def d3484 (p : Pattern) : Int := if p 161 then d3483 p else d3482 p
theorem agree3484 (p q : Pattern) (h : Agree support p q) : d3484 p = d3484 q := by
  simp only [d3484, h 161 (by decide), agree3483 p q h, agree3482 p q h]
theorem nonnegative3484 (p : Pattern) : 0 ≤ d3484 p :=
  nonnegative_ite (p 161) (nonnegative3483 p) (nonnegative3482 p)
def d3485 (p : Pattern) : Int := if p 163 then d12 p else d3382 p
theorem agree3485 (p q : Pattern) (h : Agree support p q) : d3485 p = d3485 q := by
  simp only [d3485, h 163 (by decide), agree12 p q h, agree3382 p q h]
theorem nonnegative3485 (p : Pattern) : 0 ≤ d3485 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3382 p)
def d3486 (p : Pattern) : Int := if p 162 then d3485 p else d3402 p
theorem agree3486 (p q : Pattern) (h : Agree support p q) : d3486 p = d3486 q := by
  simp only [d3486, h 162 (by decide), agree3485 p q h, agree3402 p q h]
theorem nonnegative3486 (p : Pattern) : 0 ≤ d3486 p :=
  nonnegative_ite (p 162) (nonnegative3485 p) (nonnegative3402 p)
def d3487 (p : Pattern) : Int := if p 162 then d12 p else d3485 p
theorem agree3487 (p q : Pattern) (h : Agree support p q) : d3487 p = d3487 q := by
  simp only [d3487, h 162 (by decide), agree12 p q h, agree3485 p q h]
theorem nonnegative3487 (p : Pattern) : 0 ≤ d3487 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3485 p)
def d3488 (p : Pattern) : Int := if p 161 then d3487 p else d3486 p
theorem agree3488 (p q : Pattern) (h : Agree support p q) : d3488 p = d3488 q := by
  simp only [d3488, h 161 (by decide), agree3487 p q h, agree3486 p q h]
theorem nonnegative3488 (p : Pattern) : 0 ≤ d3488 p :=
  nonnegative_ite (p 161) (nonnegative3487 p) (nonnegative3486 p)
def d3489 (p : Pattern) : Int := if p 160 then d3488 p else d3484 p
theorem agree3489 (p q : Pattern) (h : Agree support p q) : d3489 p = d3489 q := by
  simp only [d3489, h 160 (by decide), agree3488 p q h, agree3484 p q h]
theorem nonnegative3489 (p : Pattern) : 0 ≤ d3489 p :=
  nonnegative_ite (p 160) (nonnegative3488 p) (nonnegative3484 p)
def d3490 (p : Pattern) : Int := if p 141 then d3489 p else d3388 p
theorem agree3490 (p q : Pattern) (h : Agree support p q) : d3490 p = d3490 q := by
  simp only [d3490, h 141 (by decide), agree3489 p q h, agree3388 p q h]
theorem nonnegative3490 (p : Pattern) : 0 ≤ d3490 p :=
  nonnegative_ite (p 141) (nonnegative3489 p) (nonnegative3388 p)
def d3491 (p : Pattern) : Int := if p 162 then d3481 p else d3417 p
theorem agree3491 (p q : Pattern) (h : Agree support p q) : d3491 p = d3491 q := by
  simp only [d3491, h 162 (by decide), agree3481 p q h, agree3417 p q h]
theorem nonnegative3491 (p : Pattern) : 0 ≤ d3491 p :=
  nonnegative_ite (p 162) (nonnegative3481 p) (nonnegative3417 p)
def d3492 (p : Pattern) : Int := if p 161 then d3483 p else d3491 p
theorem agree3492 (p q : Pattern) (h : Agree support p q) : d3492 p = d3492 q := by
  simp only [d3492, h 161 (by decide), agree3483 p q h, agree3491 p q h]
theorem nonnegative3492 (p : Pattern) : 0 ≤ d3492 p :=
  nonnegative_ite (p 161) (nonnegative3483 p) (nonnegative3491 p)
def d3493 (p : Pattern) : Int := if p 160 then d3422 p else d3492 p
theorem agree3493 (p q : Pattern) (h : Agree support p q) : d3493 p = d3493 q := by
  simp only [d3493, h 160 (by decide), agree3422 p q h, agree3492 p q h]
theorem nonnegative3493 (p : Pattern) : 0 ≤ d3493 p :=
  nonnegative_ite (p 160) (nonnegative3422 p) (nonnegative3492 p)
def d3494 (p : Pattern) : Int := if p 141 then d3493 p else d3416 p
theorem agree3494 (p q : Pattern) (h : Agree support p q) : d3494 p = d3494 q := by
  simp only [d3494, h 141 (by decide), agree3493 p q h, agree3416 p q h]
theorem nonnegative3494 (p : Pattern) : 0 ≤ d3494 p :=
  nonnegative_ite (p 141) (nonnegative3493 p) (nonnegative3416 p)
def d3495 (p : Pattern) : Int := if p 138 then d3494 p else d3490 p
theorem agree3495 (p q : Pattern) (h : Agree support p q) : d3495 p = d3495 q := by
  simp only [d3495, h 138 (by decide), agree3494 p q h, agree3490 p q h]
theorem nonnegative3495 (p : Pattern) : 0 ≤ d3495 p :=
  nonnegative_ite (p 138) (nonnegative3494 p) (nonnegative3490 p)
def d3496 (p : Pattern) : Int := if p 138 then d3429 p else d3494 p
theorem agree3496 (p q : Pattern) (h : Agree support p q) : d3496 p = d3496 q := by
  simp only [d3496, h 138 (by decide), agree3429 p q h, agree3494 p q h]
theorem nonnegative3496 (p : Pattern) : 0 ≤ d3496 p :=
  nonnegative_ite (p 138) (nonnegative3429 p) (nonnegative3494 p)
def d3497 (p : Pattern) : Int := if p 116 then d3496 p else d3495 p
theorem agree3497 (p q : Pattern) (h : Agree support p q) : d3497 p = d3497 q := by
  simp only [d3497, h 116 (by decide), agree3496 p q h, agree3495 p q h]
theorem nonnegative3497 (p : Pattern) : 0 ≤ d3497 p :=
  nonnegative_ite (p 116) (nonnegative3496 p) (nonnegative3495 p)
def d3498 (p : Pattern) : Int := if p 182 then d3378 p else d3374 p
theorem agree3498 (p q : Pattern) (h : Agree support p q) : d3498 p = d3498 q := by
  simp only [d3498, h 182 (by decide), agree3378 p q h, agree3374 p q h]
theorem nonnegative3498 (p : Pattern) : 0 ≤ d3498 p :=
  nonnegative_ite (p 182) (nonnegative3378 p) (nonnegative3374 p)
def d3499 (p : Pattern) : Int := if p 163 then d3498 p else d3394 p
theorem agree3499 (p q : Pattern) (h : Agree support p q) : d3499 p = d3499 q := by
  simp only [d3499, h 163 (by decide), agree3498 p q h, agree3394 p q h]
theorem nonnegative3499 (p : Pattern) : 0 ≤ d3499 p :=
  nonnegative_ite (p 163) (nonnegative3498 p) (nonnegative3394 p)
def d3500 (p : Pattern) : Int := if p 162 then d3485 p else d3499 p
theorem agree3500 (p q : Pattern) (h : Agree support p q) : d3500 p = d3500 q := by
  simp only [d3500, h 162 (by decide), agree3485 p q h, agree3499 p q h]
theorem nonnegative3500 (p : Pattern) : 0 ≤ d3500 p :=
  nonnegative_ite (p 162) (nonnegative3485 p) (nonnegative3499 p)
def d3501 (p : Pattern) : Int := if p 182 then d12 p else d3377 p
theorem agree3501 (p q : Pattern) (h : Agree support p q) : d3501 p = d3501 q := by
  simp only [d3501, h 182 (by decide), agree12 p q h, agree3377 p q h]
theorem nonnegative3501 (p : Pattern) : 0 ≤ d3501 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3377 p)
def d3502 (p : Pattern) : Int := if p 163 then d12 p else d3501 p
theorem agree3502 (p q : Pattern) (h : Agree support p q) : d3502 p = d3502 q := by
  simp only [d3502, h 163 (by decide), agree12 p q h, agree3501 p q h]
theorem nonnegative3502 (p : Pattern) : 0 ≤ d3502 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3501 p)
def d3503 (p : Pattern) : Int := if p 162 then d12 p else d3502 p
theorem agree3503 (p q : Pattern) (h : Agree support p q) : d3503 p = d3503 q := by
  simp only [d3503, h 162 (by decide), agree12 p q h, agree3502 p q h]
theorem nonnegative3503 (p : Pattern) : 0 ≤ d3503 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3502 p)
def d3504 (p : Pattern) : Int := if p 161 then d3503 p else d3500 p
theorem agree3504 (p q : Pattern) (h : Agree support p q) : d3504 p = d3504 q := by
  simp only [d3504, h 161 (by decide), agree3503 p q h, agree3500 p q h]
theorem nonnegative3504 (p : Pattern) : 0 ≤ d3504 p :=
  nonnegative_ite (p 161) (nonnegative3503 p) (nonnegative3500 p)
def d3505 (p : Pattern) : Int := if p 160 then d3504 p else d3411 p
theorem agree3505 (p q : Pattern) (h : Agree support p q) : d3505 p = d3505 q := by
  simp only [d3505, h 160 (by decide), agree3504 p q h, agree3411 p q h]
theorem nonnegative3505 (p : Pattern) : 0 ≤ d3505 p :=
  nonnegative_ite (p 160) (nonnegative3504 p) (nonnegative3411 p)
def d3506 (p : Pattern) : Int := if p 182 then d3378 p else d3366 p
theorem agree3506 (p q : Pattern) (h : Agree support p q) : d3506 p = d3506 q := by
  simp only [d3506, h 182 (by decide), agree3378 p q h, agree3366 p q h]
theorem nonnegative3506 (p : Pattern) : 0 ≤ d3506 p :=
  nonnegative_ite (p 182) (nonnegative3378 p) (nonnegative3366 p)
def d3507 (p : Pattern) : Int := if p 163 then d3382 p else d3506 p
theorem agree3507 (p q : Pattern) (h : Agree support p q) : d3507 p = d3507 q := by
  simp only [d3507, h 163 (by decide), agree3382 p q h, agree3506 p q h]
theorem nonnegative3507 (p : Pattern) : 0 ≤ d3507 p :=
  nonnegative_ite (p 163) (nonnegative3382 p) (nonnegative3506 p)
def d3508 (p : Pattern) : Int := if p 162 then d3502 p else d3507 p
theorem agree3508 (p q : Pattern) (h : Agree support p q) : d3508 p = d3508 q := by
  simp only [d3508, h 162 (by decide), agree3502 p q h, agree3507 p q h]
theorem nonnegative3508 (p : Pattern) : 0 ≤ d3508 p :=
  nonnegative_ite (p 162) (nonnegative3502 p) (nonnegative3507 p)
def d3509 (p : Pattern) : Int := if p 162 then d12 p else d3266 p
theorem agree3509 (p q : Pattern) (h : Agree support p q) : d3509 p = d3509 q := by
  simp only [d3509, h 162 (by decide), agree12 p q h, agree3266 p q h]
theorem nonnegative3509 (p : Pattern) : 0 ≤ d3509 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3266 p)
def d3510 (p : Pattern) : Int := if p 161 then d3509 p else d3508 p
theorem agree3510 (p q : Pattern) (h : Agree support p q) : d3510 p = d3510 q := by
  simp only [d3510, h 161 (by decide), agree3509 p q h, agree3508 p q h]
theorem nonnegative3510 (p : Pattern) : 0 ≤ d3510 p :=
  nonnegative_ite (p 161) (nonnegative3509 p) (nonnegative3508 p)
def d3511 (p : Pattern) : Int := if p 160 then d3510 p else d3492 p
theorem agree3511 (p q : Pattern) (h : Agree support p q) : d3511 p = d3511 q := by
  simp only [d3511, h 160 (by decide), agree3510 p q h, agree3492 p q h]
theorem nonnegative3511 (p : Pattern) : 0 ≤ d3511 p :=
  nonnegative_ite (p 160) (nonnegative3510 p) (nonnegative3492 p)
def d3512 (p : Pattern) : Int := if p 141 then d3511 p else d3505 p
theorem agree3512 (p q : Pattern) (h : Agree support p q) : d3512 p = d3512 q := by
  simp only [d3512, h 141 (by decide), agree3511 p q h, agree3505 p q h]
theorem nonnegative3512 (p : Pattern) : 0 ≤ d3512 p :=
  nonnegative_ite (p 141) (nonnegative3511 p) (nonnegative3505 p)
def d3513 (p : Pattern) : Int := if p 163 then d3283 p else d3394 p
theorem agree3513 (p q : Pattern) (h : Agree support p q) : d3513 p = d3513 q := by
  simp only [d3513, h 163 (by decide), agree3283 p q h, agree3394 p q h]
theorem nonnegative3513 (p : Pattern) : 0 ≤ d3513 p :=
  nonnegative_ite (p 163) (nonnegative3283 p) (nonnegative3394 p)
def d3514 (p : Pattern) : Int := if p 162 then d3513 p else d3364 p
theorem agree3514 (p q : Pattern) (h : Agree support p q) : d3514 p = d3514 q := by
  simp only [d3514, h 162 (by decide), agree3513 p q h, agree3364 p q h]
theorem nonnegative3514 (p : Pattern) : 0 ≤ d3514 p :=
  nonnegative_ite (p 162) (nonnegative3513 p) (nonnegative3364 p)
def d3515 (p : Pattern) : Int := if p 161 then d3399 p else d3514 p
theorem agree3515 (p q : Pattern) (h : Agree support p q) : d3515 p = d3515 q := by
  simp only [d3515, h 161 (by decide), agree3399 p q h, agree3514 p q h]
theorem nonnegative3515 (p : Pattern) : 0 ≤ d3515 p :=
  nonnegative_ite (p 161) (nonnegative3399 p) (nonnegative3514 p)
def d3516 (p : Pattern) : Int := if p 160 then d3422 p else d3515 p
theorem agree3516 (p q : Pattern) (h : Agree support p q) : d3516 p = d3516 q := by
  simp only [d3516, h 160 (by decide), agree3422 p q h, agree3515 p q h]
theorem nonnegative3516 (p : Pattern) : 0 ≤ d3516 p :=
  nonnegative_ite (p 160) (nonnegative3422 p) (nonnegative3515 p)
def d3517 (p : Pattern) : Int := if p 162 then d3481 p else d3394 p
theorem agree3517 (p q : Pattern) (h : Agree support p q) : d3517 p = d3517 q := by
  simp only [d3517, h 162 (by decide), agree3481 p q h, agree3394 p q h]
theorem nonnegative3517 (p : Pattern) : 0 ≤ d3517 p :=
  nonnegative_ite (p 162) (nonnegative3481 p) (nonnegative3394 p)
def d3518 (p : Pattern) : Int := if p 161 then d3421 p else d3517 p
theorem agree3518 (p q : Pattern) (h : Agree support p q) : d3518 p = d3518 q := by
  simp only [d3518, h 161 (by decide), agree3421 p q h, agree3517 p q h]
theorem nonnegative3518 (p : Pattern) : 0 ≤ d3518 p :=
  nonnegative_ite (p 161) (nonnegative3421 p) (nonnegative3517 p)
def d3519 (p : Pattern) : Int := if p 162 then d12 p else d3247 p
theorem agree3519 (p q : Pattern) (h : Agree support p q) : d3519 p = d3519 q := by
  simp only [d3519, h 162 (by decide), agree12 p q h, agree3247 p q h]
theorem nonnegative3519 (p : Pattern) : 0 ≤ d3519 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3247 p)
def d3520 (p : Pattern) : Int := if p 161 then d12 p else d3519 p
theorem agree3520 (p q : Pattern) (h : Agree support p q) : d3520 p = d3520 q := by
  simp only [d3520, h 161 (by decide), agree12 p q h, agree3519 p q h]
theorem nonnegative3520 (p : Pattern) : 0 ≤ d3520 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3519 p)
def d3521 (p : Pattern) : Int := if p 160 then d3520 p else d3518 p
theorem agree3521 (p q : Pattern) (h : Agree support p q) : d3521 p = d3521 q := by
  simp only [d3521, h 160 (by decide), agree3520 p q h, agree3518 p q h]
theorem nonnegative3521 (p : Pattern) : 0 ≤ d3521 p :=
  nonnegative_ite (p 160) (nonnegative3520 p) (nonnegative3518 p)
def d3522 (p : Pattern) : Int := if p 141 then d3521 p else d3516 p
theorem agree3522 (p q : Pattern) (h : Agree support p q) : d3522 p = d3522 q := by
  simp only [d3522, h 141 (by decide), agree3521 p q h, agree3516 p q h]
theorem nonnegative3522 (p : Pattern) : 0 ≤ d3522 p :=
  nonnegative_ite (p 141) (nonnegative3521 p) (nonnegative3516 p)
def d3523 (p : Pattern) : Int := if p 138 then d3522 p else d3512 p
theorem agree3523 (p q : Pattern) (h : Agree support p q) : d3523 p = d3523 q := by
  simp only [d3523, h 138 (by decide), agree3522 p q h, agree3512 p q h]
theorem nonnegative3523 (p : Pattern) : 0 ≤ d3523 p :=
  nonnegative_ite (p 138) (nonnegative3522 p) (nonnegative3512 p)
def d3524 (p : Pattern) : Int := if p 163 then d3246 p else d3394 p
theorem agree3524 (p q : Pattern) (h : Agree support p q) : d3524 p = d3524 q := by
  simp only [d3524, h 163 (by decide), agree3246 p q h, agree3394 p q h]
theorem nonnegative3524 (p : Pattern) : 0 ≤ d3524 p :=
  nonnegative_ite (p 163) (nonnegative3246 p) (nonnegative3394 p)
def d3525 (p : Pattern) : Int := if p 162 then d3524 p else d3364 p
theorem agree3525 (p q : Pattern) (h : Agree support p q) : d3525 p = d3525 q := by
  simp only [d3525, h 162 (by decide), agree3524 p q h, agree3364 p q h]
theorem nonnegative3525 (p : Pattern) : 0 ≤ d3525 p :=
  nonnegative_ite (p 162) (nonnegative3524 p) (nonnegative3364 p)
def d3526 (p : Pattern) : Int := if p 163 then d3246 p else d3368 p
theorem agree3526 (p q : Pattern) (h : Agree support p q) : d3526 p = d3526 q := by
  simp only [d3526, h 163 (by decide), agree3246 p q h, agree3368 p q h]
theorem nonnegative3526 (p : Pattern) : 0 ≤ d3526 p :=
  nonnegative_ite (p 163) (nonnegative3246 p) (nonnegative3368 p)
def d3527 (p : Pattern) : Int := if p 162 then d12 p else d3526 p
theorem agree3527 (p q : Pattern) (h : Agree support p q) : d3527 p = d3527 q := by
  simp only [d3527, h 162 (by decide), agree12 p q h, agree3526 p q h]
theorem nonnegative3527 (p : Pattern) : 0 ≤ d3527 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3526 p)
def d3528 (p : Pattern) : Int := if p 161 then d3527 p else d3525 p
theorem agree3528 (p q : Pattern) (h : Agree support p q) : d3528 p = d3528 q := by
  simp only [d3528, h 161 (by decide), agree3527 p q h, agree3525 p q h]
theorem nonnegative3528 (p : Pattern) : 0 ≤ d3528 p :=
  nonnegative_ite (p 161) (nonnegative3527 p) (nonnegative3525 p)
def d3529 (p : Pattern) : Int := if p 163 then d3283 p else d3412 p
theorem agree3529 (p q : Pattern) (h : Agree support p q) : d3529 p = d3529 q := by
  simp only [d3529, h 163 (by decide), agree3283 p q h, agree3412 p q h]
theorem nonnegative3529 (p : Pattern) : 0 ≤ d3529 p :=
  nonnegative_ite (p 163) (nonnegative3283 p) (nonnegative3412 p)
def d3530 (p : Pattern) : Int := if p 162 then d12 p else d3529 p
theorem agree3530 (p q : Pattern) (h : Agree support p q) : d3530 p = d3530 q := by
  simp only [d3530, h 162 (by decide), agree12 p q h, agree3529 p q h]
theorem nonnegative3530 (p : Pattern) : 0 ≤ d3530 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3529 p)
def d3531 (p : Pattern) : Int := if p 161 then d12 p else d3530 p
theorem agree3531 (p q : Pattern) (h : Agree support p q) : d3531 p = d3531 q := by
  simp only [d3531, h 161 (by decide), agree12 p q h, agree3530 p q h]
theorem nonnegative3531 (p : Pattern) : 0 ≤ d3531 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3530 p)
def d3532 (p : Pattern) : Int := if p 160 then d3531 p else d3528 p
theorem agree3532 (p q : Pattern) (h : Agree support p q) : d3532 p = d3532 q := by
  simp only [d3532, h 160 (by decide), agree3531 p q h, agree3528 p q h]
theorem nonnegative3532 (p : Pattern) : 0 ≤ d3532 p :=
  nonnegative_ite (p 160) (nonnegative3531 p) (nonnegative3528 p)
def d3533 (p : Pattern) : Int := if p 141 then d3521 p else d3532 p
theorem agree3533 (p q : Pattern) (h : Agree support p q) : d3533 p = d3533 q := by
  simp only [d3533, h 141 (by decide), agree3521 p q h, agree3532 p q h]
theorem nonnegative3533 (p : Pattern) : 0 ≤ d3533 p :=
  nonnegative_ite (p 141) (nonnegative3521 p) (nonnegative3532 p)
def d3534 (p : Pattern) : Int := if p 138 then d12 p else d3533 p
theorem agree3534 (p q : Pattern) (h : Agree support p q) : d3534 p = d3534 q := by
  simp only [d3534, h 138 (by decide), agree12 p q h, agree3533 p q h]
theorem nonnegative3534 (p : Pattern) : 0 ≤ d3534 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative3533 p)
def d3535 (p : Pattern) : Int := if p 116 then d3534 p else d3523 p
theorem agree3535 (p q : Pattern) (h : Agree support p q) : d3535 p = d3535 q := by
  simp only [d3535, h 116 (by decide), agree3534 p q h, agree3523 p q h]
theorem nonnegative3535 (p : Pattern) : 0 ≤ d3535 p :=
  nonnegative_ite (p 116) (nonnegative3534 p) (nonnegative3523 p)
def d3536 (p : Pattern) : Int := if p 115 then d3535 p else d3497 p
theorem agree3536 (p q : Pattern) (h : Agree support p q) : d3536 p = d3536 q := by
  simp only [d3536, h 115 (by decide), agree3535 p q h, agree3497 p q h]
theorem nonnegative3536 (p : Pattern) : 0 ≤ d3536 p :=
  nonnegative_ite (p 115) (nonnegative3535 p) (nonnegative3497 p)
def d3537 (p : Pattern) : Int := if p 71 then d3536 p else d3334 p
theorem agree3537 (p q : Pattern) (h : Agree support p q) : d3537 p = d3537 q := by
  simp only [d3537, h 71 (by decide), agree3536 p q h, agree3334 p q h]
theorem nonnegative3537 (p : Pattern) : 0 ≤ d3537 p :=
  nonnegative_ite (p 71) (nonnegative3536 p) (nonnegative3334 p)
def d3538 (p : Pattern) : Int := if p 49 then d3537 p else d3480 p
theorem agree3538 (p q : Pattern) (h : Agree support p q) : d3538 p = d3538 q := by
  simp only [d3538, h 49 (by decide), agree3537 p q h, agree3480 p q h]
theorem nonnegative3538 (p : Pattern) : 0 ≤ d3538 p :=
  nonnegative_ite (p 49) (nonnegative3537 p) (nonnegative3480 p)
def d3539 (p : Pattern) : Int := if p 48 then d3538 p else d3440 p
theorem agree3539 (p q : Pattern) (h : Agree support p q) : d3539 p = d3539 q := by
  simp only [d3539, h 48 (by decide), agree3538 p q h, agree3440 p q h]
theorem nonnegative3539 (p : Pattern) : 0 ≤ d3539 p :=
  nonnegative_ite (p 48) (nonnegative3538 p) (nonnegative3440 p)
def d3540 (p : Pattern) : Int := if p 246 then d13 p else d313 p
theorem agree3540 (p q : Pattern) (h : Agree support p q) : d3540 p = d3540 q := by
  simp only [d3540, h 246 (by decide), agree13 p q h, agree313 p q h]
theorem nonnegative3540 (p : Pattern) : 0 ≤ d3540 p :=
  nonnegative_ite (p 246) (nonnegative13 p) (nonnegative313 p)
def d3541 (p : Pattern) : Int := if p 225 then d13 p else d3540 p
theorem agree3541 (p q : Pattern) (h : Agree support p q) : d3541 p = d3541 q := by
  simp only [d3541, h 225 (by decide), agree13 p q h, agree3540 p q h]
theorem nonnegative3541 (p : Pattern) : 0 ≤ d3541 p :=
  nonnegative_ite (p 225) (nonnegative13 p) (nonnegative3540 p)
def d3542 (p : Pattern) : Int := if p 224 then d13 p else d3541 p
theorem agree3542 (p q : Pattern) (h : Agree support p q) : d3542 p = d3542 q := by
  simp only [d3542, h 224 (by decide), agree13 p q h, agree3541 p q h]
theorem nonnegative3542 (p : Pattern) : 0 ≤ d3542 p :=
  nonnegative_ite (p 224) (nonnegative13 p) (nonnegative3541 p)
def d3543 (p : Pattern) : Int := if p 246 then d17 p else d13 p
theorem agree3543 (p q : Pattern) (h : Agree support p q) : d3543 p = d3543 q := by
  simp only [d3543, h 246 (by decide), agree17 p q h, agree13 p q h]
theorem nonnegative3543 (p : Pattern) : 0 ≤ d3543 p :=
  nonnegative_ite (p 246) (nonnegative17 p) (nonnegative13 p)
def d3544 (p : Pattern) : Int := if p 225 then d3543 p else d13 p
theorem agree3544 (p q : Pattern) (h : Agree support p q) : d3544 p = d3544 q := by
  simp only [d3544, h 225 (by decide), agree3543 p q h, agree13 p q h]
theorem nonnegative3544 (p : Pattern) : 0 ≤ d3544 p :=
  nonnegative_ite (p 225) (nonnegative3543 p) (nonnegative13 p)
def d3545 (p : Pattern) : Int := if p 224 then d3543 p else d3544 p
theorem agree3545 (p q : Pattern) (h : Agree support p q) : d3545 p = d3545 q := by
  simp only [d3545, h 224 (by decide), agree3543 p q h, agree3544 p q h]
theorem nonnegative3545 (p : Pattern) : 0 ≤ d3545 p :=
  nonnegative_ite (p 224) (nonnegative3543 p) (nonnegative3544 p)
def d3546 (p : Pattern) : Int := if p 204 then d3545 p else d3542 p
theorem agree3546 (p q : Pattern) (h : Agree support p q) : d3546 p = d3546 q := by
  simp only [d3546, h 204 (by decide), agree3545 p q h, agree3542 p q h]
theorem nonnegative3546 (p : Pattern) : 0 ≤ d3546 p :=
  nonnegative_ite (p 204) (nonnegative3545 p) (nonnegative3542 p)
def d3547 (p : Pattern) : Int := if p 246 then d30 p else d13 p
theorem agree3547 (p q : Pattern) (h : Agree support p q) : d3547 p = d3547 q := by
  simp only [d3547, h 246 (by decide), agree30 p q h, agree13 p q h]
theorem nonnegative3547 (p : Pattern) : 0 ≤ d3547 p :=
  nonnegative_ite (p 246) (nonnegative30 p) (nonnegative13 p)
def d3548 (p : Pattern) : Int := if p 225 then d3547 p else d13 p
theorem agree3548 (p q : Pattern) (h : Agree support p q) : d3548 p = d3548 q := by
  simp only [d3548, h 225 (by decide), agree3547 p q h, agree13 p q h]
theorem nonnegative3548 (p : Pattern) : 0 ≤ d3548 p :=
  nonnegative_ite (p 225) (nonnegative3547 p) (nonnegative13 p)
def d3549 (p : Pattern) : Int := if p 224 then d3547 p else d3548 p
theorem agree3549 (p q : Pattern) (h : Agree support p q) : d3549 p = d3549 q := by
  simp only [d3549, h 224 (by decide), agree3547 p q h, agree3548 p q h]
theorem nonnegative3549 (p : Pattern) : 0 ≤ d3549 p :=
  nonnegative_ite (p 224) (nonnegative3547 p) (nonnegative3548 p)
def d3550 (p : Pattern) : Int := if p 204 then d12 p else d3549 p
theorem agree3550 (p q : Pattern) (h : Agree support p q) : d3550 p = d3550 q := by
  simp only [d3550, h 204 (by decide), agree12 p q h, agree3549 p q h]
theorem nonnegative3550 (p : Pattern) : 0 ≤ d3550 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3549 p)
def d3551 (p : Pattern) : Int := if p 182 then d3550 p else d3546 p
theorem agree3551 (p q : Pattern) (h : Agree support p q) : d3551 p = d3551 q := by
  simp only [d3551, h 182 (by decide), agree3550 p q h, agree3546 p q h]
theorem nonnegative3551 (p : Pattern) : 0 ≤ d3551 p :=
  nonnegative_ite (p 182) (nonnegative3550 p) (nonnegative3546 p)
def d3552 (p : Pattern) : Int := if p 204 then d3545 p else d13 p
theorem agree3552 (p q : Pattern) (h : Agree support p q) : d3552 p = d3552 q := by
  simp only [d3552, h 204 (by decide), agree3545 p q h, agree13 p q h]
theorem nonnegative3552 (p : Pattern) : 0 ≤ d3552 p :=
  nonnegative_ite (p 204) (nonnegative3545 p) (nonnegative13 p)
def d3553 (p : Pattern) : Int := if p 182 then d3550 p else d3552 p
theorem agree3553 (p q : Pattern) (h : Agree support p q) : d3553 p = d3553 q := by
  simp only [d3553, h 182 (by decide), agree3550 p q h, agree3552 p q h]
theorem nonnegative3553 (p : Pattern) : 0 ≤ d3553 p :=
  nonnegative_ite (p 182) (nonnegative3550 p) (nonnegative3552 p)
def d3554 (p : Pattern) : Int := if p 163 then d3553 p else d3551 p
theorem agree3554 (p q : Pattern) (h : Agree support p q) : d3554 p = d3554 q := by
  simp only [d3554, h 163 (by decide), agree3553 p q h, agree3551 p q h]
theorem nonnegative3554 (p : Pattern) : 0 ≤ d3554 p :=
  nonnegative_ite (p 163) (nonnegative3553 p) (nonnegative3551 p)
def d3555 (p : Pattern) : Int := if p 246 then d190 p else d17 p
theorem agree3555 (p q : Pattern) (h : Agree support p q) : d3555 p = d3555 q := by
  simp only [d3555, h 246 (by decide), agree190 p q h, agree17 p q h]
theorem nonnegative3555 (p : Pattern) : 0 ≤ d3555 p :=
  nonnegative_ite (p 246) (nonnegative190 p) (nonnegative17 p)
def d3556 (p : Pattern) : Int := if p 225 then d3555 p else d17 p
theorem agree3556 (p q : Pattern) (h : Agree support p q) : d3556 p = d3556 q := by
  simp only [d3556, h 225 (by decide), agree3555 p q h, agree17 p q h]
theorem nonnegative3556 (p : Pattern) : 0 ≤ d3556 p :=
  nonnegative_ite (p 225) (nonnegative3555 p) (nonnegative17 p)
def d3557 (p : Pattern) : Int := if p 224 then d3555 p else d3556 p
theorem agree3557 (p q : Pattern) (h : Agree support p q) : d3557 p = d3557 q := by
  simp only [d3557, h 224 (by decide), agree3555 p q h, agree3556 p q h]
theorem nonnegative3557 (p : Pattern) : 0 ≤ d3557 p :=
  nonnegative_ite (p 224) (nonnegative3555 p) (nonnegative3556 p)
def d3558 (p : Pattern) : Int := if p 204 then d3557 p else d17 p
theorem agree3558 (p q : Pattern) (h : Agree support p q) : d3558 p = d3558 q := by
  simp only [d3558, h 204 (by decide), agree3557 p q h, agree17 p q h]
theorem nonnegative3558 (p : Pattern) : 0 ≤ d3558 p :=
  nonnegative_ite (p 204) (nonnegative3557 p) (nonnegative17 p)
def d3559 (p : Pattern) : Int := if p 246 then d34 p else d17 p
theorem agree3559 (p q : Pattern) (h : Agree support p q) : d3559 p = d3559 q := by
  simp only [d3559, h 246 (by decide), agree34 p q h, agree17 p q h]
theorem nonnegative3559 (p : Pattern) : 0 ≤ d3559 p :=
  nonnegative_ite (p 246) (nonnegative34 p) (nonnegative17 p)
def d3560 (p : Pattern) : Int := if p 225 then d3559 p else d17 p
theorem agree3560 (p q : Pattern) (h : Agree support p q) : d3560 p = d3560 q := by
  simp only [d3560, h 225 (by decide), agree3559 p q h, agree17 p q h]
theorem nonnegative3560 (p : Pattern) : 0 ≤ d3560 p :=
  nonnegative_ite (p 225) (nonnegative3559 p) (nonnegative17 p)
def d3561 (p : Pattern) : Int := if p 224 then d3559 p else d3560 p
theorem agree3561 (p q : Pattern) (h : Agree support p q) : d3561 p = d3561 q := by
  simp only [d3561, h 224 (by decide), agree3559 p q h, agree3560 p q h]
theorem nonnegative3561 (p : Pattern) : 0 ≤ d3561 p :=
  nonnegative_ite (p 224) (nonnegative3559 p) (nonnegative3560 p)
def d3562 (p : Pattern) : Int := if p 204 then d12 p else d3561 p
theorem agree3562 (p q : Pattern) (h : Agree support p q) : d3562 p = d3562 q := by
  simp only [d3562, h 204 (by decide), agree12 p q h, agree3561 p q h]
theorem nonnegative3562 (p : Pattern) : 0 ≤ d3562 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3561 p)
def d3563 (p : Pattern) : Int := if p 182 then d3562 p else d3558 p
theorem agree3563 (p q : Pattern) (h : Agree support p q) : d3563 p = d3563 q := by
  simp only [d3563, h 182 (by decide), agree3562 p q h, agree3558 p q h]
theorem nonnegative3563 (p : Pattern) : 0 ≤ d3563 p :=
  nonnegative_ite (p 182) (nonnegative3562 p) (nonnegative3558 p)
def d3564 (p : Pattern) : Int := if p 163 then d3563 p else d3553 p
theorem agree3564 (p q : Pattern) (h : Agree support p q) : d3564 p = d3564 q := by
  simp only [d3564, h 163 (by decide), agree3563 p q h, agree3553 p q h]
theorem nonnegative3564 (p : Pattern) : 0 ≤ d3564 p :=
  nonnegative_ite (p 163) (nonnegative3563 p) (nonnegative3553 p)
def d3565 (p : Pattern) : Int := if p 162 then d3564 p else d3554 p
theorem agree3565 (p q : Pattern) (h : Agree support p q) : d3565 p = d3565 q := by
  simp only [d3565, h 162 (by decide), agree3564 p q h, agree3554 p q h]
theorem nonnegative3565 (p : Pattern) : 0 ≤ d3565 p :=
  nonnegative_ite (p 162) (nonnegative3564 p) (nonnegative3554 p)
def d3566 (p : Pattern) : Int := if p 225 then d356 p else d23 p
theorem agree3566 (p q : Pattern) (h : Agree support p q) : d3566 p = d3566 q := by
  simp only [d3566, h 225 (by decide), agree356 p q h, agree23 p q h]
theorem nonnegative3566 (p : Pattern) : 0 ≤ d3566 p :=
  nonnegative_ite (p 225) (nonnegative356 p) (nonnegative23 p)
def d3567 (p : Pattern) : Int := if p 224 then d356 p else d3566 p
theorem agree3567 (p q : Pattern) (h : Agree support p q) : d3567 p = d3567 q := by
  simp only [d3567, h 224 (by decide), agree356 p q h, agree3566 p q h]
theorem nonnegative3567 (p : Pattern) : 0 ≤ d3567 p :=
  nonnegative_ite (p 224) (nonnegative356 p) (nonnegative3566 p)
def d3568 (p : Pattern) : Int := if p 204 then d3567 p else d23 p
theorem agree3568 (p q : Pattern) (h : Agree support p q) : d3568 p = d3568 q := by
  simp only [d3568, h 204 (by decide), agree3567 p q h, agree23 p q h]
theorem nonnegative3568 (p : Pattern) : 0 ≤ d3568 p :=
  nonnegative_ite (p 204) (nonnegative3567 p) (nonnegative23 p)
def d3569 (p : Pattern) : Int := if p 246 then d39 p else d23 p
theorem agree3569 (p q : Pattern) (h : Agree support p q) : d3569 p = d3569 q := by
  simp only [d3569, h 246 (by decide), agree39 p q h, agree23 p q h]
theorem nonnegative3569 (p : Pattern) : 0 ≤ d3569 p :=
  nonnegative_ite (p 246) (nonnegative39 p) (nonnegative23 p)
def d3570 (p : Pattern) : Int := if p 225 then d3569 p else d23 p
theorem agree3570 (p q : Pattern) (h : Agree support p q) : d3570 p = d3570 q := by
  simp only [d3570, h 225 (by decide), agree3569 p q h, agree23 p q h]
theorem nonnegative3570 (p : Pattern) : 0 ≤ d3570 p :=
  nonnegative_ite (p 225) (nonnegative3569 p) (nonnegative23 p)
def d3571 (p : Pattern) : Int := if p 224 then d3569 p else d3570 p
theorem agree3571 (p q : Pattern) (h : Agree support p q) : d3571 p = d3571 q := by
  simp only [d3571, h 224 (by decide), agree3569 p q h, agree3570 p q h]
theorem nonnegative3571 (p : Pattern) : 0 ≤ d3571 p :=
  nonnegative_ite (p 224) (nonnegative3569 p) (nonnegative3570 p)
def d3572 (p : Pattern) : Int := if p 204 then d12 p else d3571 p
theorem agree3572 (p q : Pattern) (h : Agree support p q) : d3572 p = d3572 q := by
  simp only [d3572, h 204 (by decide), agree12 p q h, agree3571 p q h]
theorem nonnegative3572 (p : Pattern) : 0 ≤ d3572 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3571 p)
def d3573 (p : Pattern) : Int := if p 182 then d3572 p else d3568 p
theorem agree3573 (p q : Pattern) (h : Agree support p q) : d3573 p = d3573 q := by
  simp only [d3573, h 182 (by decide), agree3572 p q h, agree3568 p q h]
theorem nonnegative3573 (p : Pattern) : 0 ≤ d3573 p :=
  nonnegative_ite (p 182) (nonnegative3572 p) (nonnegative3568 p)
def d3574 (p : Pattern) : Int := if p 163 then d12 p else d3573 p
theorem agree3574 (p q : Pattern) (h : Agree support p q) : d3574 p = d3574 q := by
  simp only [d3574, h 163 (by decide), agree12 p q h, agree3573 p q h]
theorem nonnegative3574 (p : Pattern) : 0 ≤ d3574 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3573 p)
def d3575 (p : Pattern) : Int := if p 162 then d3574 p else d3564 p
theorem agree3575 (p q : Pattern) (h : Agree support p q) : d3575 p = d3575 q := by
  simp only [d3575, h 162 (by decide), agree3574 p q h, agree3564 p q h]
theorem nonnegative3575 (p : Pattern) : 0 ≤ d3575 p :=
  nonnegative_ite (p 162) (nonnegative3574 p) (nonnegative3564 p)
def d3576 (p : Pattern) : Int := if p 161 then d3575 p else d3565 p
theorem agree3576 (p q : Pattern) (h : Agree support p q) : d3576 p = d3576 q := by
  simp only [d3576, h 161 (by decide), agree3575 p q h, agree3565 p q h]
theorem nonnegative3576 (p : Pattern) : 0 ≤ d3576 p :=
  nonnegative_ite (p 161) (nonnegative3575 p) (nonnegative3565 p)
def d3577 (p : Pattern) : Int := if p 246 then d34 p else d13 p
theorem agree3577 (p q : Pattern) (h : Agree support p q) : d3577 p = d3577 q := by
  simp only [d3577, h 246 (by decide), agree34 p q h, agree13 p q h]
theorem nonnegative3577 (p : Pattern) : 0 ≤ d3577 p :=
  nonnegative_ite (p 246) (nonnegative34 p) (nonnegative13 p)
def d3578 (p : Pattern) : Int := if p 225 then d3577 p else d13 p
theorem agree3578 (p q : Pattern) (h : Agree support p q) : d3578 p = d3578 q := by
  simp only [d3578, h 225 (by decide), agree3577 p q h, agree13 p q h]
theorem nonnegative3578 (p : Pattern) : 0 ≤ d3578 p :=
  nonnegative_ite (p 225) (nonnegative3577 p) (nonnegative13 p)
def d3579 (p : Pattern) : Int := if p 246 then d23 p else d13 p
theorem agree3579 (p q : Pattern) (h : Agree support p q) : d3579 p = d3579 q := by
  simp only [d3579, h 246 (by decide), agree23 p q h, agree13 p q h]
theorem nonnegative3579 (p : Pattern) : 0 ≤ d3579 p :=
  nonnegative_ite (p 246) (nonnegative23 p) (nonnegative13 p)
def d3580 (p : Pattern) : Int := if p 225 then d3579 p else d3543 p
theorem agree3580 (p q : Pattern) (h : Agree support p q) : d3580 p = d3580 q := by
  simp only [d3580, h 225 (by decide), agree3579 p q h, agree3543 p q h]
theorem nonnegative3580 (p : Pattern) : 0 ≤ d3580 p :=
  nonnegative_ite (p 225) (nonnegative3579 p) (nonnegative3543 p)
def d3581 (p : Pattern) : Int := if p 224 then d3580 p else d3578 p
theorem agree3581 (p q : Pattern) (h : Agree support p q) : d3581 p = d3581 q := by
  simp only [d3581, h 224 (by decide), agree3580 p q h, agree3578 p q h]
theorem nonnegative3581 (p : Pattern) : 0 ≤ d3581 p :=
  nonnegative_ite (p 224) (nonnegative3580 p) (nonnegative3578 p)
def d3582 (p : Pattern) : Int := if p 204 then d3581 p else d13 p
theorem agree3582 (p q : Pattern) (h : Agree support p q) : d3582 p = d3582 q := by
  simp only [d3582, h 204 (by decide), agree3581 p q h, agree13 p q h]
theorem nonnegative3582 (p : Pattern) : 0 ≤ d3582 p :=
  nonnegative_ite (p 204) (nonnegative3581 p) (nonnegative13 p)
def d3583 (p : Pattern) : Int := if p 246 then d190 p else d30 p
theorem agree3583 (p q : Pattern) (h : Agree support p q) : d3583 p = d3583 q := by
  simp only [d3583, h 246 (by decide), agree190 p q h, agree30 p q h]
theorem nonnegative3583 (p : Pattern) : 0 ≤ d3583 p :=
  nonnegative_ite (p 246) (nonnegative190 p) (nonnegative30 p)
def d3584 (p : Pattern) : Int := if p 225 then d3583 p else d30 p
theorem agree3584 (p q : Pattern) (h : Agree support p q) : d3584 p = d3584 q := by
  simp only [d3584, h 225 (by decide), agree3583 p q h, agree30 p q h]
theorem nonnegative3584 (p : Pattern) : 0 ≤ d3584 p :=
  nonnegative_ite (p 225) (nonnegative3583 p) (nonnegative30 p)
def d3585 (p : Pattern) : Int := if p 246 then d34 p else d30 p
theorem agree3585 (p q : Pattern) (h : Agree support p q) : d3585 p = d3585 q := by
  simp only [d3585, h 246 (by decide), agree34 p q h, agree30 p q h]
theorem nonnegative3585 (p : Pattern) : 0 ≤ d3585 p :=
  nonnegative_ite (p 246) (nonnegative34 p) (nonnegative30 p)
def d3586 (p : Pattern) : Int := if p 225 then d1715 p else d3585 p
theorem agree3586 (p q : Pattern) (h : Agree support p q) : d3586 p = d3586 q := by
  simp only [d3586, h 225 (by decide), agree1715 p q h, agree3585 p q h]
theorem nonnegative3586 (p : Pattern) : 0 ≤ d3586 p :=
  nonnegative_ite (p 225) (nonnegative1715 p) (nonnegative3585 p)
def d3587 (p : Pattern) : Int := if p 224 then d3586 p else d3584 p
theorem agree3587 (p q : Pattern) (h : Agree support p q) : d3587 p = d3587 q := by
  simp only [d3587, h 224 (by decide), agree3586 p q h, agree3584 p q h]
theorem nonnegative3587 (p : Pattern) : 0 ≤ d3587 p :=
  nonnegative_ite (p 224) (nonnegative3586 p) (nonnegative3584 p)
def d3588 (p : Pattern) : Int := if p 204 then d12 p else d3587 p
theorem agree3588 (p q : Pattern) (h : Agree support p q) : d3588 p = d3588 q := by
  simp only [d3588, h 204 (by decide), agree12 p q h, agree3587 p q h]
theorem nonnegative3588 (p : Pattern) : 0 ≤ d3588 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3587 p)
def d3589 (p : Pattern) : Int := if p 182 then d3588 p else d3582 p
theorem agree3589 (p q : Pattern) (h : Agree support p q) : d3589 p = d3589 q := by
  simp only [d3589, h 182 (by decide), agree3588 p q h, agree3582 p q h]
theorem nonnegative3589 (p : Pattern) : 0 ≤ d3589 p :=
  nonnegative_ite (p 182) (nonnegative3588 p) (nonnegative3582 p)
def d3590 (p : Pattern) : Int := if p 225 then d364 p else d34 p
theorem agree3590 (p q : Pattern) (h : Agree support p q) : d3590 p = d3590 q := by
  simp only [d3590, h 225 (by decide), agree364 p q h, agree34 p q h]
theorem nonnegative3590 (p : Pattern) : 0 ≤ d3590 p :=
  nonnegative_ite (p 225) (nonnegative364 p) (nonnegative34 p)
def d3591 (p : Pattern) : Int := if p 246 then d57 p else d34 p
theorem agree3591 (p q : Pattern) (h : Agree support p q) : d3591 p = d3591 q := by
  simp only [d3591, h 246 (by decide), agree57 p q h, agree34 p q h]
theorem nonnegative3591 (p : Pattern) : 0 ≤ d3591 p :=
  nonnegative_ite (p 246) (nonnegative57 p) (nonnegative34 p)
def d3592 (p : Pattern) : Int := if p 225 then d364 p else d3591 p
theorem agree3592 (p q : Pattern) (h : Agree support p q) : d3592 p = d3592 q := by
  simp only [d3592, h 225 (by decide), agree364 p q h, agree3591 p q h]
theorem nonnegative3592 (p : Pattern) : 0 ≤ d3592 p :=
  nonnegative_ite (p 225) (nonnegative364 p) (nonnegative3591 p)
def d3593 (p : Pattern) : Int := if p 224 then d3592 p else d3590 p
theorem agree3593 (p q : Pattern) (h : Agree support p q) : d3593 p = d3593 q := by
  simp only [d3593, h 224 (by decide), agree3592 p q h, agree3590 p q h]
theorem nonnegative3593 (p : Pattern) : 0 ≤ d3593 p :=
  nonnegative_ite (p 224) (nonnegative3592 p) (nonnegative3590 p)
def d3594 (p : Pattern) : Int := if p 204 then d12 p else d3593 p
theorem agree3594 (p q : Pattern) (h : Agree support p q) : d3594 p = d3594 q := by
  simp only [d3594, h 204 (by decide), agree12 p q h, agree3593 p q h]
theorem nonnegative3594 (p : Pattern) : 0 ≤ d3594 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3593 p)
def d3595 (p : Pattern) : Int := if p 182 then d3594 p else d3582 p
theorem agree3595 (p q : Pattern) (h : Agree support p q) : d3595 p = d3595 q := by
  simp only [d3595, h 182 (by decide), agree3594 p q h, agree3582 p q h]
theorem nonnegative3595 (p : Pattern) : 0 ≤ d3595 p :=
  nonnegative_ite (p 182) (nonnegative3594 p) (nonnegative3582 p)
def d3596 (p : Pattern) : Int := if p 163 then d3595 p else d3589 p
theorem agree3596 (p q : Pattern) (h : Agree support p q) : d3596 p = d3596 q := by
  simp only [d3596, h 163 (by decide), agree3595 p q h, agree3589 p q h]
theorem nonnegative3596 (p : Pattern) : 0 ≤ d3596 p :=
  nonnegative_ite (p 163) (nonnegative3595 p) (nonnegative3589 p)
def d3597 (p : Pattern) : Int := if p 225 then d327 p else d39 p
theorem agree3597 (p q : Pattern) (h : Agree support p q) : d3597 p = d3597 q := by
  simp only [d3597, h 225 (by decide), agree327 p q h, agree39 p q h]
theorem nonnegative3597 (p : Pattern) : 0 ≤ d3597 p :=
  nonnegative_ite (p 225) (nonnegative327 p) (nonnegative39 p)
def d3598 (p : Pattern) : Int := if p 224 then d327 p else d3597 p
theorem agree3598 (p q : Pattern) (h : Agree support p q) : d3598 p = d3598 q := by
  simp only [d3598, h 224 (by decide), agree327 p q h, agree3597 p q h]
theorem nonnegative3598 (p : Pattern) : 0 ≤ d3598 p :=
  nonnegative_ite (p 224) (nonnegative327 p) (nonnegative3597 p)
def d3599 (p : Pattern) : Int := if p 204 then d12 p else d3598 p
theorem agree3599 (p q : Pattern) (h : Agree support p q) : d3599 p = d3599 q := by
  simp only [d3599, h 204 (by decide), agree12 p q h, agree3598 p q h]
theorem nonnegative3599 (p : Pattern) : 0 ≤ d3599 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3598 p)
end NetHack.Sokoban22Refined85
