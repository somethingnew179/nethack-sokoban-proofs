/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions22
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s3450 (pattern : Twelve) : d1740 (change pattern 5 4) = d2529 pattern := by
  change (if pattern.d then d1738 (change pattern 5 4) else d1737 (change pattern 5 4)) = d2529 pattern
  rw [s3449, s3448]
  rfl
theorem s3451 (pattern : Twelve) : d1742 (change pattern 5 4) = d2530 pattern := by
  change (if pattern.c then d1740 (change pattern 5 4) else d1736 (change pattern 5 4)) = d2530 pattern
  rw [s3450, s3442]
  rfl
theorem s3452 (pattern : Twelve) : d1734 (change pattern 5 4) = d1289 pattern := by
  change d1300 (change pattern 5 4) = d1289 pattern
  exact s3416 pattern
theorem s3453 (pattern : Twelve) : d1252 (change pattern 5 4) = d1252 pattern := by
  change (if pattern.h then d6 (change pattern 5 4) else d822 (change pattern 5 4)) = d1252 pattern
  rw [s3278, s3445]
  rfl
theorem s3454 (pattern : Twelve) : d1626 (change pattern 5 4) = d1252 pattern := by
  change d1252 (change pattern 5 4) = d1252 pattern
  exact s3453 pattern
theorem s3455 (pattern : Twelve) : d1735 (change pattern 5 4) = d1252 pattern := by
  change d1626 (change pattern 5 4) = d1252 pattern
  exact s3454 pattern
theorem s3456 (pattern : Twelve) : d1739 (change pattern 5 4) = d2531 pattern := by
  change (if pattern.j then d1735 (change pattern 5 4) else d1734 (change pattern 5 4)) = d2531 pattern
  rw [s3455, s3452]
  rfl
theorem s3457 (pattern : Twelve) : d1741 (change pattern 5 4) = d2532 pattern := by
  change (if pattern.d then d1738 (change pattern 5 4) else d1739 (change pattern 5 4)) = d2532 pattern
  rw [s3449, s3456]
  rfl
theorem s3458 (pattern : Twelve) : d1743 (change pattern 5 4) = d2533 pattern := by
  change (if pattern.c then d1741 (change pattern 5 4) else d1736 (change pattern 5 4)) = d2533 pattern
  rw [s3457, s3442]
  rfl
theorem s3459 (pattern : Twelve) : d1744 (change pattern 5 4) = d2534 pattern := by
  change (if pattern.a then d1743 (change pattern 5 4) else d1742 (change pattern 5 4)) = d2534 pattern
  rw [s3458, s3451]
  rfl
theorem s3460 (pattern : Twelve) : d0 (change pattern 5 12) = d0 pattern := by
  rfl
theorem s3461 (pattern : Twelve) : d425 (change pattern 5 12) = d0 pattern := by
  change d0 (change pattern 5 12) = d0 pattern
  exact s3460 pattern
theorem s3462 (pattern : Twelve) : d426 (change pattern 5 12) = d0 pattern := by
  change d0 (change pattern 5 12) = d0 pattern
  exact s3460 pattern
theorem s3463 (pattern : Twelve) : d444 (change pattern 5 12) = d0 pattern := by
  change (if pattern.e then d426 (change pattern 5 12) else d425 (change pattern 5 12)) = d0 pattern
  rw [s3462, s3461]
  simp only [ite_self]
theorem s3464 (pattern : Twelve) : d2 (change pattern 5 12) = d2 pattern := by
  rfl
theorem s3465 (pattern : Twelve) : d30 (change pattern 5 12) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 5 12) else d0 (change pattern 5 12)) = d30 pattern
  rw [s3464, s3460]
  rfl
theorem s3466 (pattern : Twelve) : d3 (change pattern 5 12) = d3 pattern := by
  rfl
theorem s3467 (pattern : Twelve) : d5 (change pattern 5 12) = d5 pattern := by
  rfl
theorem s3468 (pattern : Twelve) : d12 (change pattern 5 12) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 5 12) else d3 (change pattern 5 12)) = d12 pattern
  rw [s3467, s3466]
  rfl
theorem s3469 (pattern : Twelve) : d4 (change pattern 5 12) = d4 pattern := by
  rfl
theorem s3470 (pattern : Twelve) : d6 (change pattern 5 12) = d6 pattern := by
  rfl
theorem s3471 (pattern : Twelve) : d13 (change pattern 5 12) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 5 12) else d4 (change pattern 5 12)) = d13 pattern
  rw [s3470, s3469]
  rfl
theorem s3472 (pattern : Twelve) : d20 (change pattern 5 12) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 5 12) else d12 (change pattern 5 12)) = d20 pattern
  rw [s3471, s3468]
  rfl
theorem s3473 (pattern : Twelve) : d31 (change pattern 5 12) = d31 pattern := by
  change (if pattern.i then d20 (change pattern 5 12) else d0 (change pattern 5 12)) = d31 pattern
  rw [s3472, s3460]
  rfl
theorem s3474 (pattern : Twelve) : d52 (change pattern 5 12) = d52 pattern := by
  change (if pattern.h then d31 (change pattern 5 12) else d30 (change pattern 5 12)) = d52 pattern
  rw [s3473, s3465]
  rfl
theorem s3475 (pattern : Twelve) : d427 (change pattern 5 12) = d52 pattern := by
  change d52 (change pattern 5 12) = d52 pattern
  exact s3474 pattern
theorem s3476 (pattern : Twelve) : d14 (change pattern 5 12) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 5 12) else d5 (change pattern 5 12)) = d14 pattern
  rw [s3470, s3467]
  rfl
theorem s3477 (pattern : Twelve) : d22 (change pattern 5 12) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 5 12) else d14 (change pattern 5 12)) = d22 pattern
  rw [s3470, s3476]
  rfl
theorem s3478 (pattern : Twelve) : d33 (change pattern 5 12) = d33 pattern := by
  change (if pattern.i then d22 (change pattern 5 12) else d0 (change pattern 5 12)) = d33 pattern
  rw [s3477, s3460]
  rfl
theorem s3479 (pattern : Twelve) : d54 (change pattern 5 12) = d54 pattern := by
  change (if pattern.h then d33 (change pattern 5 12) else d30 (change pattern 5 12)) = d54 pattern
  rw [s3478, s3465]
  rfl
theorem s3480 (pattern : Twelve) : d428 (change pattern 5 12) = d54 pattern := by
  change d54 (change pattern 5 12) = d54 pattern
  exact s3479 pattern
theorem s3481 (pattern : Twelve) : d445 (change pattern 5 12) = d2535 pattern := by
  change (if pattern.e then d428 (change pattern 5 12) else d427 (change pattern 5 12)) = d2535 pattern
  rw [s3480, s3475]
  rfl
theorem s3482 (pattern : Twelve) : d455 (change pattern 5 12) = d2536 pattern := by
  change (if pattern.j then d445 (change pattern 5 12) else d444 (change pattern 5 12)) = d2536 pattern
  rw [s3481, s3463]
  rfl
theorem s3483 (pattern : Twelve) : d429 (change pattern 5 12) = d0 pattern := by
  change d0 (change pattern 5 12) = d0 pattern
  exact s3460 pattern
theorem s3484 (pattern : Twelve) : d430 (change pattern 5 12) = d0 pattern := by
  change d0 (change pattern 5 12) = d0 pattern
  exact s3460 pattern
theorem s3485 (pattern : Twelve) : d446 (change pattern 5 12) = d0 pattern := by
  change (if pattern.e then d430 (change pattern 5 12) else d429 (change pattern 5 12)) = d0 pattern
  rw [s3484, s3483]
  simp only [ite_self]
theorem s3486 (pattern : Twelve) : d35 (change pattern 5 12) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 5 12) else d0 (change pattern 5 12)) = d35 pattern
  rw [s3470, s3460]
  rfl
theorem s3487 (pattern : Twelve) : d56 (change pattern 5 12) = d56 pattern := by
  change (if pattern.h then d35 (change pattern 5 12) else d30 (change pattern 5 12)) = d56 pattern
  rw [s3486, s3465]
  rfl
theorem s3488 (pattern : Twelve) : d431 (change pattern 5 12) = d56 pattern := by
  change d56 (change pattern 5 12) = d56 pattern
  exact s3487 pattern
theorem s3489 (pattern : Twelve) : d432 (change pattern 5 12) = d56 pattern := by
  change d56 (change pattern 5 12) = d56 pattern
  exact s3487 pattern
theorem s3490 (pattern : Twelve) : d447 (change pattern 5 12) = d56 pattern := by
  change (if pattern.e then d432 (change pattern 5 12) else d431 (change pattern 5 12)) = d56 pattern
  rw [s3489, s3488]
  simp only [ite_self]
theorem s3491 (pattern : Twelve) : d456 (change pattern 5 12) = d2498 pattern := by
  change (if pattern.j then d447 (change pattern 5 12) else d446 (change pattern 5 12)) = d2498 pattern
  rw [s3490, s3485]
  rfl
theorem s3492 (pattern : Twelve) : d465 (change pattern 5 12) = d2537 pattern := by
  change (if pattern.d then d456 (change pattern 5 12) else d455 (change pattern 5 12)) = d2537 pattern
  rw [s3491, s3482]
  rfl
theorem s3493 (pattern : Twelve) : d433 (change pattern 5 12) = d30 pattern := by
  change d30 (change pattern 5 12) = d30 pattern
  exact s3465 pattern
theorem s3494 (pattern : Twelve) : d434 (change pattern 5 12) = d30 pattern := by
  change d30 (change pattern 5 12) = d30 pattern
  exact s3465 pattern
theorem s3495 (pattern : Twelve) : d448 (change pattern 5 12) = d30 pattern := by
  change (if pattern.e then d434 (change pattern 5 12) else d433 (change pattern 5 12)) = d30 pattern
  rw [s3494, s3493]
  simp only [ite_self]
theorem s3496 (pattern : Twelve) : d38 (change pattern 5 12) = d38 pattern := by
  change (if pattern.i then d4 (change pattern 5 12) else d2 (change pattern 5 12)) = d38 pattern
  rw [s3469, s3464]
  rfl
theorem s3497 (pattern : Twelve) : d39 (change pattern 5 12) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 5 12) else d2 (change pattern 5 12)) = d39 pattern
  rw [s3470, s3464]
  rfl
theorem s3498 (pattern : Twelve) : d59 (change pattern 5 12) = d59 pattern := by
  change (if pattern.h then d39 (change pattern 5 12) else d38 (change pattern 5 12)) = d59 pattern
  rw [s3497, s3496]
  rfl
theorem s3499 (pattern : Twelve) : d435 (change pattern 5 12) = d59 pattern := by
  change d59 (change pattern 5 12) = d59 pattern
  exact s3498 pattern
theorem s3500 (pattern : Twelve) : d436 (change pattern 5 12) = d59 pattern := by
  change d59 (change pattern 5 12) = d59 pattern
  exact s3498 pattern
theorem s3501 (pattern : Twelve) : d449 (change pattern 5 12) = d59 pattern := by
  change (if pattern.e then d436 (change pattern 5 12) else d435 (change pattern 5 12)) = d59 pattern
  rw [s3500, s3499]
  simp only [ite_self]
theorem s3502 (pattern : Twelve) : d457 (change pattern 5 12) = d2500 pattern := by
  change (if pattern.j then d449 (change pattern 5 12) else d448 (change pattern 5 12)) = d2500 pattern
  rw [s3501, s3495]
  rfl
theorem s3503 (pattern : Twelve) : d437 (change pattern 5 12) = d56 pattern := by
  change d56 (change pattern 5 12) = d56 pattern
  exact s3487 pattern
theorem s3504 (pattern : Twelve) : d450 (change pattern 5 12) = d56 pattern := by
  change (if pattern.e then d432 (change pattern 5 12) else d437 (change pattern 5 12)) = d56 pattern
  rw [s3489, s3503]
  simp only [ite_self]
theorem s3505 (pattern : Twelve) : d458 (change pattern 5 12) = d2501 pattern := by
  change (if pattern.j then d6 (change pattern 5 12) else d450 (change pattern 5 12)) = d2501 pattern
  rw [s3470, s3504]
  rfl
theorem s3506 (pattern : Twelve) : d466 (change pattern 5 12) = d2502 pattern := by
  change (if pattern.d then d458 (change pattern 5 12) else d457 (change pattern 5 12)) = d2502 pattern
  rw [s3505, s3502]
  rfl
theorem s3507 (pattern : Twelve) : d471 (change pattern 5 12) = d2538 pattern := by
  change (if pattern.c then d466 (change pattern 5 12) else d465 (change pattern 5 12)) = d2538 pattern
  rw [s3506, s3492]
  rfl
theorem s3508 (pattern : Twelve) : d438 (change pattern 5 12) = d0 pattern := by
  change d0 (change pattern 5 12) = d0 pattern
  exact s3460 pattern
theorem s3509 (pattern : Twelve) : d439 (change pattern 5 12) = d52 pattern := by
  change d52 (change pattern 5 12) = d52 pattern
  exact s3474 pattern
theorem s3510 (pattern : Twelve) : d440 (change pattern 5 12) = d54 pattern := by
  change d54 (change pattern 5 12) = d54 pattern
  exact s3479 pattern
theorem s3511 (pattern : Twelve) : d451 (change pattern 5 12) = d2535 pattern := by
  change (if pattern.e then d440 (change pattern 5 12) else d439 (change pattern 5 12)) = d2535 pattern
  rw [s3510, s3509]
  rfl
theorem s3512 (pattern : Twelve) : d459 (change pattern 5 12) = d2536 pattern := by
  change (if pattern.j then d451 (change pattern 5 12) else d438 (change pattern 5 12)) = d2536 pattern
  rw [s3511, s3508]
  rfl
theorem s3513 (pattern : Twelve) : d460 (change pattern 5 12) = d2498 pattern := by
  change (if pattern.j then d432 (change pattern 5 12) else d438 (change pattern 5 12)) = d2498 pattern
  rw [s3489, s3508]
  rfl
theorem s3514 (pattern : Twelve) : d467 (change pattern 5 12) = d2537 pattern := by
  change (if pattern.d then d460 (change pattern 5 12) else d459 (change pattern 5 12)) = d2537 pattern
  rw [s3513, s3512]
  rfl
theorem s3515 (pattern : Twelve) : d441 (change pattern 5 12) = d30 pattern := by
  change d30 (change pattern 5 12) = d30 pattern
  exact s3465 pattern
theorem s3516 (pattern : Twelve) : d461 (change pattern 5 12) = d2500 pattern := by
  change (if pattern.j then d436 (change pattern 5 12) else d441 (change pattern 5 12)) = d2500 pattern
  rw [s3500, s3515]
  rfl
theorem s3517 (pattern : Twelve) : d462 (change pattern 5 12) = d2501 pattern := by
  change (if pattern.j then d6 (change pattern 5 12) else d432 (change pattern 5 12)) = d2501 pattern
  rw [s3470, s3489]
  rfl
theorem s3518 (pattern : Twelve) : d468 (change pattern 5 12) = d2502 pattern := by
  change (if pattern.d then d462 (change pattern 5 12) else d461 (change pattern 5 12)) = d2502 pattern
  rw [s3517, s3516]
  rfl
theorem s3519 (pattern : Twelve) : d472 (change pattern 5 12) = d2538 pattern := by
  change (if pattern.c then d468 (change pattern 5 12) else d467 (change pattern 5 12)) = d2538 pattern
  rw [s3518, s3514]
  rfl
theorem s3520 (pattern : Twelve) : d474 (change pattern 5 12) = d2538 pattern := by
  change (if pattern.g then d472 (change pattern 5 12) else d471 (change pattern 5 12)) = d2538 pattern
  rw [s3519, s3507]
  simp only [ite_self]
theorem s3521 (pattern : Twelve) : d475 (change pattern 5 12) = d2538 pattern := by
  change (if pattern.b then d472 (change pattern 5 12) else d474 (change pattern 5 12)) = d2538 pattern
  rw [s3519, s3520]
  simp only [ite_self]
theorem s3522 (pattern : Twelve) : d452 (change pattern 5 12) = d2539 pattern := by
  change (if pattern.e then d432 (change pattern 5 12) else d439 (change pattern 5 12)) = d2539 pattern
  rw [s3489, s3509]
  rfl
theorem s3523 (pattern : Twelve) : d463 (change pattern 5 12) = d2540 pattern := by
  change (if pattern.j then d452 (change pattern 5 12) else d438 (change pattern 5 12)) = d2540 pattern
  rw [s3522, s3508]
  rfl
theorem s3524 (pattern : Twelve) : d469 (change pattern 5 12) = d2541 pattern := by
  change (if pattern.d then d460 (change pattern 5 12) else d463 (change pattern 5 12)) = d2541 pattern
  rw [s3513, s3523]
  rfl
theorem s3525 (pattern : Twelve) : d123 (change pattern 5 12) = d123 pattern := by
  change (if pattern.i then d3 (change pattern 5 12) else d0 (change pattern 5 12)) = d123 pattern
  rw [s3466, s3460]
  rfl
theorem s3526 (pattern : Twelve) : d132 (change pattern 5 12) = d132 pattern := by
  change (if pattern.h then d123 (change pattern 5 12) else d30 (change pattern 5 12)) = d132 pattern
  rw [s3525, s3465]
  rfl
theorem s3527 (pattern : Twelve) : d442 (change pattern 5 12) = d132 pattern := by
  change d132 (change pattern 5 12) = d132 pattern
  exact s3526 pattern
theorem s3528 (pattern : Twelve) : d453 (change pattern 5 12) = d2542 pattern := by
  change (if pattern.e then d442 (change pattern 5 12) else d441 (change pattern 5 12)) = d2542 pattern
  rw [s3527, s3515]
  rfl
theorem s3529 (pattern : Twelve) : d126 (change pattern 5 12) = d126 pattern := by
  change (if pattern.i then d5 (change pattern 5 12) else d2 (change pattern 5 12)) = d126 pattern
  rw [s3467, s3464]
  rfl
theorem s3530 (pattern : Twelve) : d47 (change pattern 5 12) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 5 12) else d3 (change pattern 5 12)) = d47 pattern
  rw [s3470, s3466]
  rfl
theorem s3531 (pattern : Twelve) : d134 (change pattern 5 12) = d134 pattern := by
  change (if pattern.h then d47 (change pattern 5 12) else d126 (change pattern 5 12)) = d134 pattern
  rw [s3530, s3529]
  rfl
theorem s3532 (pattern : Twelve) : d443 (change pattern 5 12) = d134 pattern := by
  change d134 (change pattern 5 12) = d134 pattern
  exact s3531 pattern
theorem s3533 (pattern : Twelve) : d454 (change pattern 5 12) = d2543 pattern := by
  change (if pattern.e then d443 (change pattern 5 12) else d436 (change pattern 5 12)) = d2543 pattern
  rw [s3532, s3500]
  rfl
theorem s3534 (pattern : Twelve) : d464 (change pattern 5 12) = d2544 pattern := by
  change (if pattern.j then d454 (change pattern 5 12) else d453 (change pattern 5 12)) = d2544 pattern
  rw [s3533, s3528]
  rfl
theorem s3535 (pattern : Twelve) : d470 (change pattern 5 12) = d2545 pattern := by
  change (if pattern.d then d462 (change pattern 5 12) else d464 (change pattern 5 12)) = d2545 pattern
  rw [s3517, s3534]
  rfl
theorem s3536 (pattern : Twelve) : d473 (change pattern 5 12) = d2546 pattern := by
  change (if pattern.c then d470 (change pattern 5 12) else d469 (change pattern 5 12)) = d2546 pattern
  rw [s3535, s3524]
  rfl
theorem s3537 (pattern : Twelve) : d476 (change pattern 5 12) = d2547 pattern := by
  change (if pattern.a then d473 (change pattern 5 12) else d475 (change pattern 5 12)) = d2547 pattern
  rw [s3536, s3521]
  rfl
theorem s3538 (pattern : Twelve) : d1 (change pattern 5 12) = d1 pattern := by
  rfl
theorem s3539 (pattern : Twelve) : d7 (change pattern 5 12) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 5 12) else d0 (change pattern 5 12)) = d7 pattern
  rw [s3538, s3460]
  rfl
theorem s3540 (pattern : Twelve) : d17 (change pattern 5 12) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 5 12) else d0 (change pattern 5 12)) = d17 pattern
  rw [s3539, s3460]
  rfl
theorem s3541 (pattern : Twelve) : d1070 (change pattern 5 12) = d17 pattern := by
  change d17 (change pattern 5 12) = d17 pattern
  exact s3540 pattern
theorem s3542 (pattern : Twelve) : d1078 (change pattern 5 12) = d2548 pattern := by
  change (if pattern.e then d1070 (change pattern 5 12) else d426 (change pattern 5 12)) = d2548 pattern
  rw [s3541, s3462]
  rfl
theorem s3543 (pattern : Twelve) : d1071 (change pattern 5 12) = d56 pattern := by
  change d56 (change pattern 5 12) = d56 pattern
  exact s3487 pattern
theorem s3544 (pattern : Twelve) : d9 (change pattern 5 12) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 5 12) else d2 (change pattern 5 12)) = d9 pattern
  rw [s3466, s3464]
  rfl
theorem s3545 (pattern : Twelve) : d23 (change pattern 5 12) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 5 12) else d2 (change pattern 5 12)) = d23 pattern
  rw [s3544, s3464]
  rfl
theorem s3546 (pattern : Twelve) : d34 (change pattern 5 12) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 5 12) else d17 (change pattern 5 12)) = d34 pattern
  rw [s3545, s3540]
  rfl
theorem s3547 (pattern : Twelve) : d36 (change pattern 5 12) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 5 12) else d17 (change pattern 5 12)) = d36 pattern
  rw [s3470, s3540]
  rfl
theorem s3548 (pattern : Twelve) : d827 (change pattern 5 12) = d827 pattern := by
  change (if pattern.h then d36 (change pattern 5 12) else d34 (change pattern 5 12)) = d827 pattern
  rw [s3547, s3546]
  rfl
theorem s3549 (pattern : Twelve) : d1072 (change pattern 5 12) = d827 pattern := by
  change d827 (change pattern 5 12) = d827 pattern
  exact s3548 pattern
theorem s3550 (pattern : Twelve) : d1079 (change pattern 5 12) = d2549 pattern := by
  change (if pattern.e then d1072 (change pattern 5 12) else d1071 (change pattern 5 12)) = d2549 pattern
  rw [s3549, s3543]
  rfl
theorem s3551 (pattern : Twelve) : d1088 (change pattern 5 12) = d2550 pattern := by
  change (if pattern.j then d1079 (change pattern 5 12) else d1078 (change pattern 5 12)) = d2550 pattern
  rw [s3550, s3542]
  rfl
theorem s3552 (pattern : Twelve) : d1073 (change pattern 5 12) = d17 pattern := by
  change d17 (change pattern 5 12) = d17 pattern
  exact s3540 pattern
theorem s3553 (pattern : Twelve) : d1080 (change pattern 5 12) = d2548 pattern := by
  change (if pattern.e then d1073 (change pattern 5 12) else d430 (change pattern 5 12)) = d2548 pattern
  rw [s3552, s3484]
  rfl
theorem s3554 (pattern : Twelve) : d1081 (change pattern 5 12) = d2549 pattern := by
  change (if pattern.e then d1072 (change pattern 5 12) else d432 (change pattern 5 12)) = d2549 pattern
  rw [s3549, s3489]
  rfl
theorem s3555 (pattern : Twelve) : d1089 (change pattern 5 12) = d2550 pattern := by
  change (if pattern.j then d1081 (change pattern 5 12) else d1080 (change pattern 5 12)) = d2550 pattern
  rw [s3554, s3553]
  rfl
theorem s3556 (pattern : Twelve) : d1095 (change pattern 5 12) = d2550 pattern := by
  change (if pattern.d then d1089 (change pattern 5 12) else d1088 (change pattern 5 12)) = d2550 pattern
  rw [s3555, s3551]
  simp only [ite_self]
theorem s3557 (pattern : Twelve) : d1074 (change pattern 5 12) = d34 pattern := by
  change d34 (change pattern 5 12) = d34 pattern
  exact s3546 pattern
theorem s3558 (pattern : Twelve) : d1082 (change pattern 5 12) = d2551 pattern := by
  change (if pattern.e then d1074 (change pattern 5 12) else d434 (change pattern 5 12)) = d2551 pattern
  rw [s3557, s3494]
  rfl
theorem s3559 (pattern : Twelve) : d15 (change pattern 5 12) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 5 12) else d4 (change pattern 5 12)) = d15 pattern
  rw [s3467, s3469]
  rfl
theorem s3560 (pattern : Twelve) : d24 (change pattern 5 12) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 5 12) else d4 (change pattern 5 12)) = d24 pattern
  rw [s3559, s3469]
  rfl
theorem s3561 (pattern : Twelve) : d41 (change pattern 5 12) = d41 pattern := by
  change (if pattern.i then d24 (change pattern 5 12) else d23 (change pattern 5 12)) = d41 pattern
  rw [s3560, s3545]
  rfl
theorem s3562 (pattern : Twelve) : d40 (change pattern 5 12) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 5 12) else d23 (change pattern 5 12)) = d40 pattern
  rw [s3470, s3545]
  rfl
theorem s3563 (pattern : Twelve) : d830 (change pattern 5 12) = d830 pattern := by
  change (if pattern.h then d40 (change pattern 5 12) else d41 (change pattern 5 12)) = d830 pattern
  rw [s3562, s3561]
  rfl
theorem s3564 (pattern : Twelve) : d1075 (change pattern 5 12) = d830 pattern := by
  change d830 (change pattern 5 12) = d830 pattern
  exact s3563 pattern
theorem s3565 (pattern : Twelve) : d1083 (change pattern 5 12) = d2552 pattern := by
  change (if pattern.e then d1075 (change pattern 5 12) else d436 (change pattern 5 12)) = d2552 pattern
  rw [s3564, s3500]
  rfl
theorem s3566 (pattern : Twelve) : d1090 (change pattern 5 12) = d2553 pattern := by
  change (if pattern.j then d1083 (change pattern 5 12) else d1082 (change pattern 5 12)) = d2553 pattern
  rw [s3565, s3558]
  rfl
theorem s3567 (pattern : Twelve) : d1091 (change pattern 5 12) = d2554 pattern := by
  change (if pattern.j then d6 (change pattern 5 12) else d1081 (change pattern 5 12)) = d2554 pattern
  rw [s3470, s3554]
  rfl
theorem s3568 (pattern : Twelve) : d1096 (change pattern 5 12) = d2555 pattern := by
  change (if pattern.d then d1091 (change pattern 5 12) else d1090 (change pattern 5 12)) = d2555 pattern
  rw [s3567, s3566]
  rfl
theorem s3569 (pattern : Twelve) : d1099 (change pattern 5 12) = d2556 pattern := by
  change (if pattern.c then d1096 (change pattern 5 12) else d1095 (change pattern 5 12)) = d2556 pattern
  rw [s3568, s3556]
  rfl
theorem s3570 (pattern : Twelve) : d1084 (change pattern 5 12) = d2548 pattern := by
  change (if pattern.e then d1073 (change pattern 5 12) else d438 (change pattern 5 12)) = d2548 pattern
  rw [s3552, s3508]
  rfl
theorem s3571 (pattern : Twelve) : d1092 (change pattern 5 12) = d2550 pattern := by
  change (if pattern.j then d1081 (change pattern 5 12) else d1084 (change pattern 5 12)) = d2550 pattern
  rw [s3554, s3570]
  rfl
theorem s3572 (pattern : Twelve) : d1085 (change pattern 5 12) = d2551 pattern := by
  change (if pattern.e then d1074 (change pattern 5 12) else d441 (change pattern 5 12)) = d2551 pattern
  rw [s3557, s3515]
  rfl
theorem s3573 (pattern : Twelve) : d1093 (change pattern 5 12) = d2553 pattern := by
  change (if pattern.j then d1083 (change pattern 5 12) else d1085 (change pattern 5 12)) = d2553 pattern
  rw [s3565, s3572]
  rfl
theorem s3574 (pattern : Twelve) : d1097 (change pattern 5 12) = d2555 pattern := by
  change (if pattern.d then d1091 (change pattern 5 12) else d1093 (change pattern 5 12)) = d2555 pattern
  rw [s3567, s3573]
  rfl
theorem s3575 (pattern : Twelve) : d1100 (change pattern 5 12) = d2556 pattern := by
  change (if pattern.c then d1097 (change pattern 5 12) else d1092 (change pattern 5 12)) = d2556 pattern
  rw [s3574, s3571]
  rfl
theorem s3576 (pattern : Twelve) : d1102 (change pattern 5 12) = d2556 pattern := by
  change (if pattern.g then d1100 (change pattern 5 12) else d1099 (change pattern 5 12)) = d2556 pattern
  rw [s3575, s3569]
  simp only [ite_self]
theorem s3577 (pattern : Twelve) : d1103 (change pattern 5 12) = d2556 pattern := by
  change (if pattern.b then d1100 (change pattern 5 12) else d1102 (change pattern 5 12)) = d2556 pattern
  rw [s3575, s3576]
  simp only [ite_self]
theorem s3578 (pattern : Twelve) : d117 (change pattern 5 12) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 5 12) else d3 (change pattern 5 12)) = d117 pattern
  rw [s3469, s3466]
  rfl
theorem s3579 (pattern : Twelve) : d119 (change pattern 5 12) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 5 12) else d3 (change pattern 5 12)) = d119 pattern
  rw [s3578, s3466]
  rfl
theorem s3580 (pattern : Twelve) : d879 (change pattern 5 12) = d879 pattern := by
  change (if pattern.i then d119 (change pattern 5 12) else d17 (change pattern 5 12)) = d879 pattern
  rw [s3579, s3540]
  rfl
theorem s3581 (pattern : Twelve) : d886 (change pattern 5 12) = d886 pattern := by
  change (if pattern.h then d879 (change pattern 5 12) else d34 (change pattern 5 12)) = d886 pattern
  rw [s3580, s3546]
  rfl
theorem s3582 (pattern : Twelve) : d1076 (change pattern 5 12) = d886 pattern := by
  change d886 (change pattern 5 12) = d886 pattern
  exact s3581 pattern
theorem s3583 (pattern : Twelve) : d1086 (change pattern 5 12) = d2557 pattern := by
  change (if pattern.e then d1076 (change pattern 5 12) else d441 (change pattern 5 12)) = d2557 pattern
  rw [s3582, s3515]
  rfl
theorem s3584 (pattern : Twelve) : d118 (change pattern 5 12) = d118 pattern := by
  change (if pattern.k then d14 (change pattern 5 12) else d5 (change pattern 5 12)) = d118 pattern
  rw [s3476, s3467]
  rfl
theorem s3585 (pattern : Twelve) : d881 (change pattern 5 12) = d881 pattern := by
  change (if pattern.i then d118 (change pattern 5 12) else d23 (change pattern 5 12)) = d881 pattern
  rw [s3584, s3545]
  rfl
theorem s3586 (pattern : Twelve) : d125 (change pattern 5 12) = d125 pattern := by
  change (if pattern.i then d6 (change pattern 5 12) else d119 (change pattern 5 12)) = d125 pattern
  rw [s3470, s3579]
  rfl
theorem s3587 (pattern : Twelve) : d888 (change pattern 5 12) = d888 pattern := by
  change (if pattern.h then d125 (change pattern 5 12) else d881 (change pattern 5 12)) = d888 pattern
  rw [s3586, s3585]
  rfl
theorem s3588 (pattern : Twelve) : d1077 (change pattern 5 12) = d888 pattern := by
  change d888 (change pattern 5 12) = d888 pattern
  exact s3587 pattern
theorem s3589 (pattern : Twelve) : d1087 (change pattern 5 12) = d2558 pattern := by
  change (if pattern.e then d1077 (change pattern 5 12) else d436 (change pattern 5 12)) = d2558 pattern
  rw [s3588, s3500]
  rfl
theorem s3590 (pattern : Twelve) : d1094 (change pattern 5 12) = d2559 pattern := by
  change (if pattern.j then d1087 (change pattern 5 12) else d1086 (change pattern 5 12)) = d2559 pattern
  rw [s3589, s3583]
  rfl
theorem s3591 (pattern : Twelve) : d1098 (change pattern 5 12) = d2560 pattern := by
  change (if pattern.d then d1091 (change pattern 5 12) else d1094 (change pattern 5 12)) = d2560 pattern
  rw [s3567, s3590]
  rfl
theorem s3592 (pattern : Twelve) : d1101 (change pattern 5 12) = d2561 pattern := by
  change (if pattern.c then d1098 (change pattern 5 12) else d1092 (change pattern 5 12)) = d2561 pattern
  rw [s3591, s3571]
  rfl
theorem s3593 (pattern : Twelve) : d1104 (change pattern 5 12) = d2562 pattern := by
  change (if pattern.a then d1101 (change pattern 5 12) else d1103 (change pattern 5 12)) = d2562 pattern
  rw [s3592, s3577]
  rfl
theorem s3594 (pattern : Twelve) : d10 (change pattern 5 12) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 5 12) else d0 (change pattern 5 12)) = d10 pattern
  rw [s3464, s3460]
  rfl
theorem s3595 (pattern : Twelve) : d11 (change pattern 5 12) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 5 12) else d1 (change pattern 5 12)) = d11 pattern
  rw [s3466, s3538]
  rfl
theorem s3596 (pattern : Twelve) : d19 (change pattern 5 12) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 5 12) else d10 (change pattern 5 12)) = d19 pattern
  rw [s3595, s3594]
  rfl
theorem s3597 (pattern : Twelve) : d1294 (change pattern 5 12) = d19 pattern := by
  change d19 (change pattern 5 12) = d19 pattern
  exact s3596 pattern
theorem s3598 (pattern : Twelve) : d1472 (change pattern 5 12) = d2563 pattern := by
  change (if pattern.e then d1294 (change pattern 5 12) else d1070 (change pattern 5 12)) = d2563 pattern
  rw [s3597, s3541]
  rfl
theorem s3599 (pattern : Twelve) : d16 (change pattern 5 12) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 5 12) else d2 (change pattern 5 12)) = d16 pattern
  rw [s3469, s3464]
  rfl
end NetHack.Sokoban21.Diagram
