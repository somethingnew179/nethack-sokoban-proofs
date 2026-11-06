/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions27
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub3360 (p : Pattern) : d468 (change p 139 (some 113)) = d1102 p := by
  change (if p 132 then d467 (change p 139 (some 113)) else d462 (change p 139 (some 113))) = d1102 p
  rw [sub3359, sub3344]
  rfl
theorem sub3361 (p : Pattern) : d469 (change p 139 (some 113)) = d8 p := by
  change (if p 134 then d52 (change p 139 (some 113)) else d460 (change p 139 (some 113))) = d8 p
  rw [sub3333, sub3337]
  simp only [ite_self]
theorem sub3362 (p : Pattern) : d470 (change p 139 (some 113)) = d1097 p := by
  change (if p 134 then d54 (change p 139 (some 113)) else d52 (change p 139 (some 113))) = d1097 p
  rw [sub3342, sub3333]
  rfl
theorem sub3363 (p : Pattern) : d471 (change p 139 (some 113)) = d1098 p := by
  change (if p 133 then d470 (change p 139 (some 113)) else d469 (change p 139 (some 113))) = d1098 p
  rw [sub3362, sub3361]
  rfl
theorem sub3364 (p : Pattern) : d472 (change p 139 (some 113)) = d1099 p := by
  change (if p 134 then d58 (change p 139 (some 113)) else d460 (change p 139 (some 113))) = d1099 p
  rw [sub3351, sub3337]
  rfl
theorem sub3365 (p : Pattern) : d473 (change p 139 (some 113)) = d1100 p := by
  change (if p 134 then d54 (change p 139 (some 113)) else d61 (change p 139 (some 113))) = d1100 p
  rw [sub3342, sub3356]
  rfl
theorem sub3366 (p : Pattern) : d474 (change p 139 (some 113)) = d1101 p := by
  change (if p 133 then d473 (change p 139 (some 113)) else d472 (change p 139 (some 113))) = d1101 p
  rw [sub3365, sub3364]
  rfl
theorem sub3367 (p : Pattern) : d475 (change p 139 (some 113)) = d1102 p := by
  change (if p 132 then d474 (change p 139 (some 113)) else d471 (change p 139 (some 113))) = d1102 p
  rw [sub3366, sub3363]
  rfl
theorem sub3368 (p : Pattern) : d476 (change p 139 (some 113)) = d1102 p := by
  change (if p 112 then d475 (change p 139 (some 113)) else d468 (change p 139 (some 113))) = d1102 p
  rw [sub3367, sub3360]
  simp only [ite_self]
theorem sub3369 (p : Pattern) : d483 (change p 139 (some 113)) = d8 p := by
  change d8 (change p 139 (some 113)) = d8 p
  exact sub3331 p
theorem sub3370 (p : Pattern) : d484 (change p 139 (some 113)) = d8 p := by
  change (if p 138 then d52 (change p 139 (some 113)) else d483 (change p 139 (some 113))) = d8 p
  rw [sub3333, sub3369]
  simp only [ite_self]
theorem sub3371 (p : Pattern) : d485 (change p 139 (some 113)) = d1097 p := by
  change (if p 134 then d54 (change p 139 (some 113)) else d484 (change p 139 (some 113))) = d1097 p
  rw [sub3342, sub3370]
  rfl
theorem sub3372 (p : Pattern) : d9 (change p 139 (some 113)) = d9 p := by
  change (if p 161 then d2 (change p 139 (some 113)) else d1 (change p 139 (some 113))) = d9 p
  rw [sub3325, sub3345]
  rfl
theorem sub3373 (p : Pattern) : d10 (change p 139 (some 113)) = d10 p := by
  change (if p 160 then d9 (change p 139 (some 113)) else d1 (change p 139 (some 113))) = d10 p
  rw [sub3372, sub3345]
  rfl
theorem sub3374 (p : Pattern) : d11 (change p 139 (some 113)) = d11 p := by
  change (if p 160 then d2 (change p 139 (some 113)) else d1 (change p 139 (some 113))) = d11 p
  rw [sub3325, sub3345]
  rfl
theorem sub3375 (p : Pattern) : d12 (change p 139 (some 113)) = d12 p := by
  change (if p 159 then d11 (change p 139 (some 113)) else d10 (change p 139 (some 113))) = d12 p
  rw [sub3374, sub3373]
  rfl
theorem sub3376 (p : Pattern) : d39 (change p 139 (some 113)) = d39 p := by
  change (if p 159 then d2 (change p 139 (some 113)) else d11 (change p 139 (some 113))) = d39 p
  rw [sub3325, sub3374]
  rfl
theorem sub3377 (p : Pattern) : d40 (change p 139 (some 113)) = d40 p := by
  change (if p 158 then d39 (change p 139 (some 113)) else d12 (change p 139 (some 113))) = d40 p
  rw [sub3376, sub3375]
  rfl
theorem sub3378 (p : Pattern) : d68 (change p 139 (some 113)) = d40 p := by
  change d40 (change p 139 (some 113)) = d40 p
  exact sub3377 p
theorem sub3379 (p : Pattern) : d21 (change p 139 (some 113)) = d21 p := by
  change (if p 160 then d2 (change p 139 (some 113)) else d9 (change p 139 (some 113))) = d21 p
  rw [sub3325, sub3372]
  rfl
theorem sub3380 (p : Pattern) : d22 (change p 139 (some 113)) = d22 p := by
  change (if p 159 then d21 (change p 139 (some 113)) else d10 (change p 139 (some 113))) = d22 p
  rw [sub3379, sub3373]
  rfl
theorem sub3381 (p : Pattern) : d23 (change p 139 (some 113)) = d23 p := by
  change (if p 159 then d2 (change p 139 (some 113)) else d21 (change p 139 (some 113))) = d23 p
  rw [sub3325, sub3379]
  rfl
theorem sub3382 (p : Pattern) : d24 (change p 139 (some 113)) = d24 p := by
  change (if p 158 then d23 (change p 139 (some 113)) else d22 (change p 139 (some 113))) = d24 p
  rw [sub3381, sub3380]
  rfl
theorem sub3383 (p : Pattern) : d70 (change p 139 (some 113)) = d24 p := by
  change d24 (change p 139 (some 113)) = d24 p
  exact sub3382 p
theorem sub3384 (p : Pattern) : d75 (change p 139 (some 113)) = d1103 p := by
  change (if p 134 then d70 (change p 139 (some 113)) else d68 (change p 139 (some 113))) = d1103 p
  rw [sub3383, sub3378]
  rfl
theorem sub3385 (p : Pattern) : d486 (change p 139 (some 113)) = d1104 p := by
  change (if p 133 then d75 (change p 139 (some 113)) else d485 (change p 139 (some 113))) = d1104 p
  rw [sub3384, sub3371]
  rfl
theorem sub3386 (p : Pattern) : d487 (change p 139 (some 113)) = d1105 p := by
  change (if p 132 then d486 (change p 139 (some 113)) else d462 (change p 139 (some 113))) = d1105 p
  rw [sub3385, sub3344]
  rfl
theorem sub3387 (p : Pattern) : d488 (change p 139 (some 113)) = d1105 p := by
  change d487 (change p 139 (some 113)) = d1105 p
  exact sub3386 p
theorem sub3388 (p : Pattern) : d491 (change p 139 (some 113)) = d1104 p := by
  change (if p 133 then d75 (change p 139 (some 113)) else d470 (change p 139 (some 113))) = d1104 p
  rw [sub3384, sub3362]
  rfl
theorem sub3389 (p : Pattern) : d492 (change p 139 (some 113)) = d1105 p := by
  change (if p 132 then d491 (change p 139 (some 113)) else d471 (change p 139 (some 113))) = d1105 p
  rw [sub3388, sub3363]
  rfl
theorem sub3390 (p : Pattern) : d493 (change p 139 (some 113)) = d1105 p := by
  change d492 (change p 139 (some 113)) = d1105 p
  exact sub3389 p
theorem sub3391 (p : Pattern) : d494 (change p 139 (some 113)) = d1105 p := by
  change (if p 112 then d493 (change p 139 (some 113)) else d488 (change p 139 (some 113))) = d1105 p
  rw [sub3390, sub3387]
  simp only [ite_self]
theorem sub3392 (p : Pattern) : d495 (change p 139 (some 113)) = d1106 p := by
  change (if p 106 then d494 (change p 139 (some 113)) else d476 (change p 139 (some 113))) = d1106 p
  rw [sub3391, sub3368]
  rfl
theorem sub3393 (p : Pattern) : d496 (change p 139 (some 113)) = d1099 p := by
  change (if p 134 then d58 (change p 139 (some 113)) else d484 (change p 139 (some 113))) = d1099 p
  rw [sub3351, sub3370]
  rfl
theorem sub3394 (p : Pattern) : d497 (change p 139 (some 113)) = d1101 p := by
  change (if p 133 then d473 (change p 139 (some 113)) else d496 (change p 139 (some 113))) = d1101 p
  rw [sub3365, sub3393]
  rfl
theorem sub3395 (p : Pattern) : d498 (change p 139 (some 113)) = d1102 p := by
  change (if p 132 then d497 (change p 139 (some 113)) else d462 (change p 139 (some 113))) = d1102 p
  rw [sub3394, sub3344]
  rfl
theorem sub3396 (p : Pattern) : d499 (change p 139 (some 113)) = d1102 p := by
  change d498 (change p 139 (some 113)) = d1102 p
  exact sub3395 p
theorem sub3397 (p : Pattern) : d13 (change p 139 (some 113)) = d13 p := by
  change (if p 159 then d2 (change p 139 (some 113)) else d10 (change p 139 (some 113))) = d13 p
  rw [sub3325, sub3373]
  rfl
theorem sub3398 (p : Pattern) : d14 (change p 139 (some 113)) = d14 p := by
  change (if p 158 then d13 (change p 139 (some 113)) else d12 (change p 139 (some 113))) = d14 p
  rw [sub3397, sub3375]
  rfl
theorem sub3399 (p : Pattern) : d500 (change p 139 (some 113)) = d14 p := by
  change d14 (change p 139 (some 113)) = d14 p
  exact sub3398 p
theorem sub3400 (p : Pattern) : d97 (change p 139 (some 113)) = d14 p := by
  change d14 (change p 139 (some 113)) = d14 p
  exact sub3398 p
theorem sub3401 (p : Pattern) : d501 (change p 139 (some 113)) = d14 p := by
  change (if p 138 then d97 (change p 139 (some 113)) else d500 (change p 139 (some 113))) = d14 p
  rw [sub3400, sub3399]
  simp only [ite_self]
theorem sub3402 (p : Pattern) : d502 (change p 139 (some 113)) = d14 p := by
  change (if p 134 then d97 (change p 139 (some 113)) else d501 (change p 139 (some 113))) = d14 p
  rw [sub3400, sub3401]
  simp only [ite_self]
theorem sub3403 (p : Pattern) : d109 (change p 139 (some 113)) = d1107 p := by
  change (if p 134 then d70 (change p 139 (some 113)) else d97 (change p 139 (some 113))) = d1107 p
  rw [sub3383, sub3400]
  rfl
theorem sub3404 (p : Pattern) : d503 (change p 139 (some 113)) = d1108 p := by
  change (if p 133 then d109 (change p 139 (some 113)) else d502 (change p 139 (some 113))) = d1108 p
  rw [sub3403, sub3402]
  rfl
theorem sub3405 (p : Pattern) : d125 (change p 139 (some 113)) = d1109 p := by
  change (if p 133 then d75 (change p 139 (some 113)) else d109 (change p 139 (some 113))) = d1109 p
  rw [sub3384, sub3403]
  rfl
theorem sub3406 (p : Pattern) : d507 (change p 139 (some 113)) = d1110 p := by
  change (if p 132 then d125 (change p 139 (some 113)) else d503 (change p 139 (some 113))) = d1110 p
  rw [sub3405, sub3404]
  rfl
theorem sub3407 (p : Pattern) : d508 (change p 139 (some 113)) = d1110 p := by
  change d507 (change p 139 (some 113)) = d1110 p
  exact sub3406 p
theorem sub3408 (p : Pattern) : d509 (change p 139 (some 113)) = d1111 p := by
  change (if p 112 then d508 (change p 139 (some 113)) else d499 (change p 139 (some 113))) = d1111 p
  rw [sub3407, sub3396]
  rfl
theorem sub3409 (p : Pattern) : d510 (change p 139 (some 113)) = d8 p := by
  change (if p 134 then d52 (change p 139 (some 113)) else d484 (change p 139 (some 113))) = d8 p
  rw [sub3333, sub3370]
  simp only [ite_self]
theorem sub3410 (p : Pattern) : d511 (change p 139 (some 113)) = d1098 p := by
  change (if p 133 then d470 (change p 139 (some 113)) else d510 (change p 139 (some 113))) = d1098 p
  rw [sub3362, sub3409]
  rfl
theorem sub3411 (p : Pattern) : d512 (change p 139 (some 113)) = d1105 p := by
  change (if p 132 then d491 (change p 139 (some 113)) else d511 (change p 139 (some 113))) = d1105 p
  rw [sub3388, sub3410]
  rfl
theorem sub3412 (p : Pattern) : d513 (change p 139 (some 113)) = d1105 p := by
  change d512 (change p 139 (some 113)) = d1105 p
  exact sub3411 p
theorem sub3413 (p : Pattern) : d110 (change p 139 (some 113)) = d1108 p := by
  change (if p 133 then d109 (change p 139 (some 113)) else d97 (change p 139 (some 113))) = d1108 p
  rw [sub3403, sub3400]
  rfl
theorem sub3414 (p : Pattern) : d111 (change p 139 (some 113)) = d1112 p := by
  change (if p 133 then d2 (change p 139 (some 113)) else d109 (change p 139 (some 113))) = d1112 p
  rw [sub3325, sub3403]
  rfl
theorem sub3415 (p : Pattern) : d112 (change p 139 (some 113)) = d1113 p := by
  change (if p 132 then d111 (change p 139 (some 113)) else d110 (change p 139 (some 113))) = d1113 p
  rw [sub3414, sub3413]
  rfl
theorem sub3416 (p : Pattern) : d515 (change p 139 (some 113)) = d1113 p := by
  change d112 (change p 139 (some 113)) = d1113 p
  exact sub3415 p
theorem sub3417 (p : Pattern) : d516 (change p 139 (some 113)) = d1114 p := by
  change (if p 112 then d515 (change p 139 (some 113)) else d513 (change p 139 (some 113))) = d1114 p
  rw [sub3416, sub3412]
  rfl
theorem sub3418 (p : Pattern) : d517 (change p 139 (some 113)) = d1115 p := by
  change (if p 106 then d516 (change p 139 (some 113)) else d509 (change p 139 (some 113))) = d1115 p
  rw [sub3417, sub3408]
  rfl
theorem sub3419 (p : Pattern) : d518 (change p 139 (some 113)) = d1116 p := by
  change (if p 86 then d517 (change p 139 (some 113)) else d495 (change p 139 (some 113))) = d1116 p
  rw [sub3418, sub3392]
  rfl
theorem sub3420 (p : Pattern) : d519 (change p 139 (some 113)) = d1099 p := by
  change (if p 134 then d58 (change p 139 (some 113)) else d52 (change p 139 (some 113))) = d1099 p
  rw [sub3351, sub3333]
  rfl
theorem sub3421 (p : Pattern) : d520 (change p 139 (some 113)) = d1101 p := by
  change (if p 133 then d473 (change p 139 (some 113)) else d519 (change p 139 (some 113))) = d1101 p
  rw [sub3365, sub3420]
  rfl
theorem sub3422 (p : Pattern) : d521 (change p 139 (some 113)) = d1102 p := by
  change (if p 132 then d520 (change p 139 (some 113)) else d471 (change p 139 (some 113))) = d1102 p
  rw [sub3421, sub3363]
  rfl
theorem sub3423 (p : Pattern) : d522 (change p 139 (some 113)) = d1102 p := by
  change d521 (change p 139 (some 113)) = d1102 p
  exact sub3422 p
theorem sub3424 (p : Pattern) : d523 (change p 139 (some 113)) = d1102 p := by
  change (if p 112 then d522 (change p 139 (some 113)) else d499 (change p 139 (some 113))) = d1102 p
  rw [sub3423, sub3396]
  simp only [ite_self]
theorem sub3425 (p : Pattern) : d524 (change p 139 (some 113)) = d1098 p := by
  change (if p 133 then d470 (change p 139 (some 113)) else d52 (change p 139 (some 113))) = d1098 p
  rw [sub3362, sub3333]
  rfl
theorem sub3426 (p : Pattern) : d525 (change p 139 (some 113)) = d1105 p := by
  change (if p 132 then d491 (change p 139 (some 113)) else d524 (change p 139 (some 113))) = d1105 p
  rw [sub3388, sub3425]
  rfl
theorem sub3427 (p : Pattern) : d526 (change p 139 (some 113)) = d1105 p := by
  change d525 (change p 139 (some 113)) = d1105 p
  exact sub3426 p
theorem sub3428 (p : Pattern) : d527 (change p 139 (some 113)) = d1105 p := by
  change (if p 112 then d526 (change p 139 (some 113)) else d513 (change p 139 (some 113))) = d1105 p
  rw [sub3427, sub3412]
  simp only [ite_self]
theorem sub3429 (p : Pattern) : d528 (change p 139 (some 113)) = d1106 p := by
  change (if p 106 then d527 (change p 139 (some 113)) else d523 (change p 139 (some 113))) = d1106 p
  rw [sub3428, sub3424]
  rfl
theorem sub3430 (p : Pattern) : d529 (change p 139 (some 113)) = d1102 p := by
  change (if p 132 then d520 (change p 139 (some 113)) else d511 (change p 139 (some 113))) = d1102 p
  rw [sub3421, sub3410]
  rfl
theorem sub3431 (p : Pattern) : d530 (change p 139 (some 113)) = d1102 p := by
  change d529 (change p 139 (some 113)) = d1102 p
  exact sub3430 p
theorem sub3432 (p : Pattern) : d126 (change p 139 (some 113)) = d1110 p := by
  change (if p 132 then d125 (change p 139 (some 113)) else d110 (change p 139 (some 113))) = d1110 p
  rw [sub3405, sub3413]
  rfl
theorem sub3433 (p : Pattern) : d531 (change p 139 (some 113)) = d1110 p := by
  change d126 (change p 139 (some 113)) = d1110 p
  exact sub3432 p
theorem sub3434 (p : Pattern) : d532 (change p 139 (some 113)) = d1111 p := by
  change (if p 112 then d531 (change p 139 (some 113)) else d530 (change p 139 (some 113))) = d1111 p
  rw [sub3433, sub3431]
  rfl
theorem sub3435 (p : Pattern) : d533 (change p 139 (some 113)) = d1105 p := by
  change d525 (change p 139 (some 113)) = d1105 p
  exact sub3426 p
theorem sub3436 (p : Pattern) : d130 (change p 139 (some 113)) = d2 p := by
  change d2 (change p 139 (some 113)) = d2 p
  exact sub3325 p
theorem sub3437 (p : Pattern) : d534 (change p 139 (some 113)) = d1939 p := by
  change (if p 112 then d130 (change p 139 (some 113)) else d533 (change p 139 (some 113))) = d1939 p
  rw [sub3436, sub3435]
  rfl
theorem sub3438 (p : Pattern) : d535 (change p 139 (some 113)) = d1940 p := by
  change (if p 106 then d534 (change p 139 (some 113)) else d532 (change p 139 (some 113))) = d1940 p
  rw [sub3437, sub3434]
  rfl
theorem sub3439 (p : Pattern) : d536 (change p 139 (some 113)) = d1941 p := by
  change (if p 86 then d535 (change p 139 (some 113)) else d528 (change p 139 (some 113))) = d1941 p
  rw [sub3438, sub3429]
  rfl
theorem sub3440 (p : Pattern) : d537 (change p 139 (some 113)) = d1942 p := by
  change (if p 80 then d536 (change p 139 (some 113)) else d518 (change p 139 (some 113))) = d1942 p
  rw [sub3439, sub3419]
  rfl
end NetHack.Sokoban32Refined
