/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions23
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s3600 (pattern : Twelve) : d25 (change pattern 5 12) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 5 12) else d16 (change pattern 5 12)) = d25 pattern
  rw [s3468, s3599]
  rfl
theorem s3601 (pattern : Twelve) : d817 (change pattern 5 12) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 5 12) else d19 (change pattern 5 12)) = d817 pattern
  rw [s3600, s3596]
  rfl
theorem s3602 (pattern : Twelve) : d29 (change pattern 5 12) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 5 12) else d19 (change pattern 5 12)) = d29 pattern
  rw [s3470, s3596]
  rfl
theorem s3603 (pattern : Twelve) : d1286 (change pattern 5 12) = d1286 pattern := by
  change (if pattern.h then d29 (change pattern 5 12) else d817 (change pattern 5 12)) = d1286 pattern
  rw [s3602, s3601]
  rfl
theorem s3604 (pattern : Twelve) : d1296 (change pattern 5 12) = d1286 pattern := by
  change d1286 (change pattern 5 12) = d1286 pattern
  exact s3603 pattern
theorem s3605 (pattern : Twelve) : d1473 (change pattern 5 12) = d2564 pattern := by
  change (if pattern.e then d1296 (change pattern 5 12) else d1072 (change pattern 5 12)) = d2564 pattern
  rw [s3604, s3549]
  rfl
theorem s3606 (pattern : Twelve) : d1479 (change pattern 5 12) = d2565 pattern := by
  change (if pattern.j then d1473 (change pattern 5 12) else d1472 (change pattern 5 12)) = d2565 pattern
  rw [s3605, s3598]
  rfl
theorem s3607 (pattern : Twelve) : d1474 (change pattern 5 12) = d2563 pattern := by
  change (if pattern.e then d1294 (change pattern 5 12) else d1073 (change pattern 5 12)) = d2563 pattern
  rw [s3597, s3552]
  rfl
theorem s3608 (pattern : Twelve) : d1480 (change pattern 5 12) = d2565 pattern := by
  change (if pattern.j then d1473 (change pattern 5 12) else d1474 (change pattern 5 12)) = d2565 pattern
  rw [s3605, s3607]
  rfl
theorem s3609 (pattern : Twelve) : d1484 (change pattern 5 12) = d2565 pattern := by
  change (if pattern.d then d1480 (change pattern 5 12) else d1479 (change pattern 5 12)) = d2565 pattern
  rw [s3608, s3606]
  simp only [ite_self]
theorem s3610 (pattern : Twelve) : d1298 (change pattern 5 12) = d817 pattern := by
  change d817 (change pattern 5 12) = d817 pattern
  exact s3601 pattern
theorem s3611 (pattern : Twelve) : d1475 (change pattern 5 12) = d2566 pattern := by
  change (if pattern.e then d1298 (change pattern 5 12) else d1074 (change pattern 5 12)) = d2566 pattern
  rw [s3610, s3557]
  rfl
theorem s3612 (pattern : Twelve) : d21 (change pattern 5 12) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 5 12) else d13 (change pattern 5 12)) = d21 pattern
  rw [s3476, s3471]
  rfl
theorem s3613 (pattern : Twelve) : d821 (change pattern 5 12) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 5 12) else d25 (change pattern 5 12)) = d821 pattern
  rw [s3612, s3600]
  rfl
theorem s3614 (pattern : Twelve) : d42 (change pattern 5 12) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 5 12) else d25 (change pattern 5 12)) = d42 pattern
  rw [s3470, s3600]
  rfl
theorem s3615 (pattern : Twelve) : d1289 (change pattern 5 12) = d1289 pattern := by
  change (if pattern.h then d42 (change pattern 5 12) else d821 (change pattern 5 12)) = d1289 pattern
  rw [s3614, s3613]
  rfl
theorem s3616 (pattern : Twelve) : d1300 (change pattern 5 12) = d1289 pattern := by
  change d1289 (change pattern 5 12) = d1289 pattern
  exact s3615 pattern
theorem s3617 (pattern : Twelve) : d1476 (change pattern 5 12) = d2567 pattern := by
  change (if pattern.e then d1300 (change pattern 5 12) else d1075 (change pattern 5 12)) = d2567 pattern
  rw [s3616, s3564]
  rfl
theorem s3618 (pattern : Twelve) : d1481 (change pattern 5 12) = d2568 pattern := by
  change (if pattern.j then d1476 (change pattern 5 12) else d1475 (change pattern 5 12)) = d2568 pattern
  rw [s3617, s3611]
  rfl
theorem s3619 (pattern : Twelve) : d1482 (change pattern 5 12) = d2569 pattern := by
  change (if pattern.j then d6 (change pattern 5 12) else d1473 (change pattern 5 12)) = d2569 pattern
  rw [s3470, s3605]
  rfl
theorem s3620 (pattern : Twelve) : d1485 (change pattern 5 12) = d2570 pattern := by
  change (if pattern.d then d1482 (change pattern 5 12) else d1481 (change pattern 5 12)) = d2570 pattern
  rw [s3619, s3618]
  rfl
theorem s3621 (pattern : Twelve) : d1487 (change pattern 5 12) = d2571 pattern := by
  change (if pattern.c then d1485 (change pattern 5 12) else d1484 (change pattern 5 12)) = d2571 pattern
  rw [s3620, s3609]
  rfl
theorem s3622 (pattern : Twelve) : d1488 (change pattern 5 12) = d2571 pattern := by
  change (if pattern.c then d1485 (change pattern 5 12) else d1480 (change pattern 5 12)) = d2571 pattern
  rw [s3620, s3608]
  rfl
theorem s3623 (pattern : Twelve) : d1490 (change pattern 5 12) = d2571 pattern := by
  change (if pattern.g then d1488 (change pattern 5 12) else d1487 (change pattern 5 12)) = d2571 pattern
  rw [s3622, s3621]
  simp only [ite_self]
theorem s3624 (pattern : Twelve) : d1491 (change pattern 5 12) = d2571 pattern := by
  change (if pattern.b then d1488 (change pattern 5 12) else d1490 (change pattern 5 12)) = d2571 pattern
  rw [s3622, s3623]
  simp only [ite_self]
theorem s3625 (pattern : Twelve) : d1329 (change pattern 5 12) = d1329 pattern := by
  change (if pattern.i then d20 (change pattern 5 12) else d19 (change pattern 5 12)) = d1329 pattern
  rw [s3472, s3596]
  rfl
theorem s3626 (pattern : Twelve) : d1336 (change pattern 5 12) = d1336 pattern := by
  change (if pattern.h then d1329 (change pattern 5 12) else d817 (change pattern 5 12)) = d1336 pattern
  rw [s3625, s3601]
  rfl
theorem s3627 (pattern : Twelve) : d1342 (change pattern 5 12) = d1336 pattern := by
  change d1336 (change pattern 5 12) = d1336 pattern
  exact s3626 pattern
theorem s3628 (pattern : Twelve) : d1477 (change pattern 5 12) = d2572 pattern := by
  change (if pattern.e then d1342 (change pattern 5 12) else d1074 (change pattern 5 12)) = d2572 pattern
  rw [s3627, s3557]
  rfl
theorem s3629 (pattern : Twelve) : d1332 (change pattern 5 12) = d1332 pattern := by
  change (if pattern.i then d22 (change pattern 5 12) else d25 (change pattern 5 12)) = d1332 pattern
  rw [s3477, s3600]
  rfl
theorem s3630 (pattern : Twelve) : d128 (change pattern 5 12) = d128 pattern := by
  change (if pattern.i then d6 (change pattern 5 12) else d20 (change pattern 5 12)) = d128 pattern
  rw [s3470, s3472]
  rfl
theorem s3631 (pattern : Twelve) : d1338 (change pattern 5 12) = d1338 pattern := by
  change (if pattern.h then d128 (change pattern 5 12) else d1332 (change pattern 5 12)) = d1338 pattern
  rw [s3630, s3629]
  rfl
theorem s3632 (pattern : Twelve) : d1344 (change pattern 5 12) = d1338 pattern := by
  change d1338 (change pattern 5 12) = d1338 pattern
  exact s3631 pattern
theorem s3633 (pattern : Twelve) : d1478 (change pattern 5 12) = d2573 pattern := by
  change (if pattern.e then d1344 (change pattern 5 12) else d1075 (change pattern 5 12)) = d2573 pattern
  rw [s3632, s3564]
  rfl
theorem s3634 (pattern : Twelve) : d1483 (change pattern 5 12) = d2574 pattern := by
  change (if pattern.j then d1478 (change pattern 5 12) else d1477 (change pattern 5 12)) = d2574 pattern
  rw [s3633, s3628]
  rfl
theorem s3635 (pattern : Twelve) : d1486 (change pattern 5 12) = d2575 pattern := by
  change (if pattern.d then d1482 (change pattern 5 12) else d1483 (change pattern 5 12)) = d2575 pattern
  rw [s3619, s3634]
  rfl
theorem s3636 (pattern : Twelve) : d1489 (change pattern 5 12) = d2576 pattern := by
  change (if pattern.c then d1486 (change pattern 5 12) else d1480 (change pattern 5 12)) = d2576 pattern
  rw [s3635, s3608]
  rfl
theorem s3637 (pattern : Twelve) : d1492 (change pattern 5 12) = d2577 pattern := by
  change (if pattern.a then d1489 (change pattern 5 12) else d1491 (change pattern 5 12)) = d2577 pattern
  rw [s3636, s3624]
  rfl
theorem s3638 (pattern : Twelve) : d1650 (change pattern 5 12) = d25 pattern := by
  change d25 (change pattern 5 12) = d25 pattern
  exact s3600 pattern
theorem s3639 (pattern : Twelve) : d1730 (change pattern 5 12) = d2578 pattern := by
  change (if pattern.e then d1650 (change pattern 5 12) else d1294 (change pattern 5 12)) = d2578 pattern
  rw [s3638, s3597]
  rfl
theorem s3640 (pattern : Twelve) : d1731 (change pattern 5 12) = d2579 pattern := by
  change (if pattern.e then d1300 (change pattern 5 12) else d1296 (change pattern 5 12)) = d2579 pattern
  rw [s3616, s3604]
  rfl
theorem s3641 (pattern : Twelve) : d1736 (change pattern 5 12) = d2580 pattern := by
  change (if pattern.j then d1731 (change pattern 5 12) else d1730 (change pattern 5 12)) = d2580 pattern
  rw [s3640, s3639]
  rfl
theorem s3642 (pattern : Twelve) : d1653 (change pattern 5 12) = d821 pattern := by
  change d821 (change pattern 5 12) = d821 pattern
  exact s3613 pattern
theorem s3643 (pattern : Twelve) : d1732 (change pattern 5 12) = d2581 pattern := by
  change (if pattern.e then d1653 (change pattern 5 12) else d1298 (change pattern 5 12)) = d2581 pattern
  rw [s3642, s3610]
  rfl
theorem s3644 (pattern : Twelve) : d822 (change pattern 5 12) = d822 pattern := by
  change (if pattern.i then d6 (change pattern 5 12) else d21 (change pattern 5 12)) = d822 pattern
  rw [s3470, s3612]
  rfl
theorem s3645 (pattern : Twelve) : d1655 (change pattern 5 12) = d822 pattern := by
  change d822 (change pattern 5 12) = d822 pattern
  exact s3644 pattern
theorem s3646 (pattern : Twelve) : d1733 (change pattern 5 12) = d2582 pattern := by
  change (if pattern.e then d1655 (change pattern 5 12) else d1300 (change pattern 5 12)) = d2582 pattern
  rw [s3645, s3616]
  rfl
theorem s3647 (pattern : Twelve) : d1737 (change pattern 5 12) = d2583 pattern := by
  change (if pattern.j then d1733 (change pattern 5 12) else d1732 (change pattern 5 12)) = d2583 pattern
  rw [s3646, s3643]
  rfl
theorem s3648 (pattern : Twelve) : d1738 (change pattern 5 12) = d2584 pattern := by
  change (if pattern.j then d6 (change pattern 5 12) else d1731 (change pattern 5 12)) = d2584 pattern
  rw [s3470, s3640]
  rfl
theorem s3649 (pattern : Twelve) : d1740 (change pattern 5 12) = d2585 pattern := by
  change (if pattern.d then d1738 (change pattern 5 12) else d1737 (change pattern 5 12)) = d2585 pattern
  rw [s3648, s3647]
  rfl
theorem s3650 (pattern : Twelve) : d1742 (change pattern 5 12) = d2586 pattern := by
  change (if pattern.c then d1740 (change pattern 5 12) else d1736 (change pattern 5 12)) = d2586 pattern
  rw [s3649, s3641]
  rfl
theorem s3651 (pattern : Twelve) : d1734 (change pattern 5 12) = d2587 pattern := by
  change (if pattern.e then d1300 (change pattern 5 12) else d1298 (change pattern 5 12)) = d2587 pattern
  rw [s3616, s3610]
  rfl
theorem s3652 (pattern : Twelve) : d1252 (change pattern 5 12) = d1252 pattern := by
  change (if pattern.h then d6 (change pattern 5 12) else d822 (change pattern 5 12)) = d1252 pattern
  rw [s3470, s3644]
  rfl
theorem s3653 (pattern : Twelve) : d1626 (change pattern 5 12) = d1252 pattern := by
  change d1252 (change pattern 5 12) = d1252 pattern
  exact s3652 pattern
theorem s3654 (pattern : Twelve) : d1735 (change pattern 5 12) = d2588 pattern := by
  change (if pattern.e then d1626 (change pattern 5 12) else d1300 (change pattern 5 12)) = d2588 pattern
  rw [s3653, s3616]
  rfl
theorem s3655 (pattern : Twelve) : d1739 (change pattern 5 12) = d2589 pattern := by
  change (if pattern.j then d1735 (change pattern 5 12) else d1734 (change pattern 5 12)) = d2589 pattern
  rw [s3654, s3651]
  rfl
theorem s3656 (pattern : Twelve) : d1741 (change pattern 5 12) = d2590 pattern := by
  change (if pattern.d then d1738 (change pattern 5 12) else d1739 (change pattern 5 12)) = d2590 pattern
  rw [s3648, s3655]
  rfl
theorem s3657 (pattern : Twelve) : d1743 (change pattern 5 12) = d2591 pattern := by
  change (if pattern.c then d1741 (change pattern 5 12) else d1736 (change pattern 5 12)) = d2591 pattern
  rw [s3656, s3641]
  rfl
theorem s3658 (pattern : Twelve) : d1744 (change pattern 5 12) = d2592 pattern := by
  change (if pattern.a then d1743 (change pattern 5 12) else d1742 (change pattern 5 12)) = d2592 pattern
  rw [s3657, s3650]
  rfl
theorem s3659 (pattern : Twelve) : d0 (change pattern 10 12) = d0 pattern := by
  rfl
theorem s3660 (pattern : Twelve) : d477 (change pattern 10 12) = d0 pattern := by
  change d0 (change pattern 10 12) = d0 pattern
  exact s3659 pattern
theorem s3661 (pattern : Twelve) : d498 (change pattern 10 12) = d0 pattern := by
  change (if pattern.i then d477 (change pattern 10 12) else d0 (change pattern 10 12)) = d0 pattern
  rw [s3660, s3659]
  simp only [ite_self]
theorem s3662 (pattern : Twelve) : d478 (change pattern 10 12) = d0 pattern := by
  change d0 (change pattern 10 12) = d0 pattern
  exact s3659 pattern
theorem s3663 (pattern : Twelve) : d499 (change pattern 10 12) = d0 pattern := by
  change (if pattern.i then d478 (change pattern 10 12) else d0 (change pattern 10 12)) = d0 pattern
  rw [s3662, s3659]
  simp only [ite_self]
theorem s3664 (pattern : Twelve) : d532 (change pattern 10 12) = d0 pattern := by
  change (if pattern.h then d499 (change pattern 10 12) else d498 (change pattern 10 12)) = d0 pattern
  rw [s3663, s3661]
  simp only [ite_self]
theorem s3665 (pattern : Twelve) : d1 (change pattern 10 12) = d1 pattern := by
  rfl
theorem s3666 (pattern : Twelve) : d161 (change pattern 10 12) = d1 pattern := by
  change d1 (change pattern 10 12) = d1 pattern
  exact s3665 pattern
theorem s3667 (pattern : Twelve) : d171 (change pattern 10 12) = d26 pattern := by
  change (if pattern.i then d161 (change pattern 10 12) else d0 (change pattern 10 12)) = d26 pattern
  rw [s3666, s3659]
  rfl
theorem s3668 (pattern : Twelve) : d162 (change pattern 10 12) = d0 pattern := by
  change d0 (change pattern 10 12) = d0 pattern
  exact s3659 pattern
theorem s3669 (pattern : Twelve) : d479 (change pattern 10 12) = d1 pattern := by
  change d1 (change pattern 10 12) = d1 pattern
  exact s3665 pattern
theorem s3670 (pattern : Twelve) : d500 (change pattern 10 12) = d26 pattern := by
  change (if pattern.i then d479 (change pattern 10 12) else d162 (change pattern 10 12)) = d26 pattern
  rw [s3669, s3668]
  rfl
theorem s3671 (pattern : Twelve) : d533 (change pattern 10 12) = d26 pattern := by
  change (if pattern.h then d500 (change pattern 10 12) else d171 (change pattern 10 12)) = d26 pattern
  rw [s3670, s3667]
  simp only [ite_self]
theorem s3672 (pattern : Twelve) : d561 (change pattern 10 12) = d2593 pattern := by
  change (if pattern.f then d533 (change pattern 10 12) else d532 (change pattern 10 12)) = d2593 pattern
  rw [s3671, s3664]
  rfl
theorem s3673 (pattern : Twelve) : d480 (change pattern 10 12) = d0 pattern := by
  change d0 (change pattern 10 12) = d0 pattern
  exact s3659 pattern
theorem s3674 (pattern : Twelve) : d501 (change pattern 10 12) = d0 pattern := by
  change (if pattern.i then d480 (change pattern 10 12) else d162 (change pattern 10 12)) = d0 pattern
  rw [s3673, s3668]
  simp only [ite_self]
theorem s3675 (pattern : Twelve) : d534 (change pattern 10 12) = d0 pattern := by
  change (if pattern.h then d501 (change pattern 10 12) else d499 (change pattern 10 12)) = d0 pattern
  rw [s3674, s3663]
  simp only [ite_self]
theorem s3676 (pattern : Twelve) : d2 (change pattern 10 12) = d2 pattern := by
  rfl
theorem s3677 (pattern : Twelve) : d8 (change pattern 10 12) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 10 12) else d1 (change pattern 10 12)) = d8 pattern
  rw [s3676, s3665]
  rfl
theorem s3678 (pattern : Twelve) : d481 (change pattern 10 12) = d8 pattern := by
  change d8 (change pattern 10 12) = d8 pattern
  exact s3677 pattern
theorem s3679 (pattern : Twelve) : d502 (change pattern 10 12) = d2594 pattern := by
  change (if pattern.i then d481 (change pattern 10 12) else d162 (change pattern 10 12)) = d2594 pattern
  rw [s3678, s3668]
  rfl
theorem s3680 (pattern : Twelve) : d10 (change pattern 10 12) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 10 12) else d0 (change pattern 10 12)) = d10 pattern
  rw [s3676, s3659]
  rfl
theorem s3681 (pattern : Twelve) : d482 (change pattern 10 12) = d10 pattern := by
  change d10 (change pattern 10 12) = d10 pattern
  exact s3680 pattern
theorem s3682 (pattern : Twelve) : d6 (change pattern 10 12) = d6 pattern := by
  rfl
theorem s3683 (pattern : Twelve) : d503 (change pattern 10 12) = d2595 pattern := by
  change (if pattern.i then d6 (change pattern 10 12) else d482 (change pattern 10 12)) = d2595 pattern
  rw [s3682, s3681]
  rfl
theorem s3684 (pattern : Twelve) : d535 (change pattern 10 12) = d2596 pattern := by
  change (if pattern.h then d503 (change pattern 10 12) else d502 (change pattern 10 12)) = d2596 pattern
  rw [s3683, s3679]
  rfl
theorem s3685 (pattern : Twelve) : d562 (change pattern 10 12) = d2597 pattern := by
  change (if pattern.f then d535 (change pattern 10 12) else d534 (change pattern 10 12)) = d2597 pattern
  rw [s3684, s3675]
  rfl
theorem s3686 (pattern : Twelve) : d588 (change pattern 10 12) = d2598 pattern := by
  change (if pattern.e then d562 (change pattern 10 12) else d561 (change pattern 10 12)) = d2598 pattern
  rw [s3685, s3672]
  rfl
theorem s3687 (pattern : Twelve) : d483 (change pattern 10 12) = d0 pattern := by
  change d0 (change pattern 10 12) = d0 pattern
  exact s3659 pattern
theorem s3688 (pattern : Twelve) : d484 (change pattern 10 12) = d2 pattern := by
  change d2 (change pattern 10 12) = d2 pattern
  exact s3676 pattern
theorem s3689 (pattern : Twelve) : d504 (change pattern 10 12) = d30 pattern := by
  change (if pattern.i then d484 (change pattern 10 12) else d483 (change pattern 10 12)) = d30 pattern
  rw [s3688, s3687]
  rfl
theorem s3690 (pattern : Twelve) : d485 (change pattern 10 12) = d0 pattern := by
  change d0 (change pattern 10 12) = d0 pattern
  exact s3659 pattern
theorem s3691 (pattern : Twelve) : d3 (change pattern 10 12) = d3 pattern := by
  rfl
theorem s3692 (pattern : Twelve) : d5 (change pattern 10 12) = d5 pattern := by
  rfl
theorem s3693 (pattern : Twelve) : d12 (change pattern 10 12) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 10 12) else d3 (change pattern 10 12)) = d12 pattern
  rw [s3692, s3691]
  rfl
theorem s3694 (pattern : Twelve) : d486 (change pattern 10 12) = d12 pattern := by
  change d12 (change pattern 10 12) = d12 pattern
  exact s3693 pattern
theorem s3695 (pattern : Twelve) : d505 (change pattern 10 12) = d2599 pattern := by
  change (if pattern.i then d486 (change pattern 10 12) else d485 (change pattern 10 12)) = d2599 pattern
  rw [s3694, s3690]
  rfl
theorem s3696 (pattern : Twelve) : d536 (change pattern 10 12) = d2600 pattern := by
  change (if pattern.h then d505 (change pattern 10 12) else d504 (change pattern 10 12)) = d2600 pattern
  rw [s3695, s3689]
  rfl
theorem s3697 (pattern : Twelve) : d487 (change pattern 10 12) = d2 pattern := by
  change d2 (change pattern 10 12) = d2 pattern
  exact s3676 pattern
theorem s3698 (pattern : Twelve) : d506 (change pattern 10 12) = d30 pattern := by
  change (if pattern.i then d487 (change pattern 10 12) else d485 (change pattern 10 12)) = d30 pattern
  rw [s3697, s3690]
  rfl
theorem s3699 (pattern : Twelve) : d4 (change pattern 10 12) = d4 pattern := by
  rfl
theorem s3700 (pattern : Twelve) : d13 (change pattern 10 12) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 10 12) else d4 (change pattern 10 12)) = d13 pattern
  rw [s3682, s3699]
  rfl
theorem s3701 (pattern : Twelve) : d170 (change pattern 10 12) = d13 pattern := by
  change d13 (change pattern 10 12) = d13 pattern
  exact s3700 pattern
theorem s3702 (pattern : Twelve) : d507 (change pattern 10 12) = d2065 pattern := by
  change (if pattern.i then d170 (change pattern 10 12) else d480 (change pattern 10 12)) = d2065 pattern
  rw [s3701, s3673]
  rfl
theorem s3703 (pattern : Twelve) : d537 (change pattern 10 12) = d2066 pattern := by
  change (if pattern.h then d507 (change pattern 10 12) else d506 (change pattern 10 12)) = d2066 pattern
  rw [s3702, s3698]
  rfl
theorem s3704 (pattern : Twelve) : d563 (change pattern 10 12) = d2601 pattern := by
  change (if pattern.f then d537 (change pattern 10 12) else d536 (change pattern 10 12)) = d2601 pattern
  rw [s3703, s3696]
  rfl
theorem s3705 (pattern : Twelve) : d14 (change pattern 10 12) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 10 12) else d5 (change pattern 10 12)) = d14 pattern
  rw [s3682, s3692]
  rfl
theorem s3706 (pattern : Twelve) : d22 (change pattern 10 12) = d14 pattern := by
  change d14 (change pattern 10 12) = d14 pattern
  exact s3705 pattern
theorem s3707 (pattern : Twelve) : d508 (change pattern 10 12) = d2602 pattern := by
  change (if pattern.i then d22 (change pattern 10 12) else d480 (change pattern 10 12)) = d2602 pattern
  rw [s3706, s3673]
  rfl
theorem s3708 (pattern : Twelve) : d538 (change pattern 10 12) = d2603 pattern := by
  change (if pattern.h then d508 (change pattern 10 12) else d506 (change pattern 10 12)) = d2603 pattern
  rw [s3707, s3698]
  rfl
theorem s3709 (pattern : Twelve) : d509 (change pattern 10 12) = d30 pattern := by
  change (if pattern.i then d487 (change pattern 10 12) else d480 (change pattern 10 12)) = d30 pattern
  rw [s3697, s3673]
  rfl
theorem s3710 (pattern : Twelve) : d539 (change pattern 10 12) = d2604 pattern := by
  change (if pattern.h then d503 (change pattern 10 12) else d509 (change pattern 10 12)) = d2604 pattern
  rw [s3683, s3709]
  rfl
theorem s3711 (pattern : Twelve) : d564 (change pattern 10 12) = d2605 pattern := by
  change (if pattern.f then d539 (change pattern 10 12) else d538 (change pattern 10 12)) = d2605 pattern
  rw [s3710, s3708]
  rfl
theorem s3712 (pattern : Twelve) : d589 (change pattern 10 12) = d2606 pattern := by
  change (if pattern.e then d564 (change pattern 10 12) else d563 (change pattern 10 12)) = d2606 pattern
  rw [s3711, s3704]
  rfl
theorem s3713 (pattern : Twelve) : d606 (change pattern 10 12) = d2607 pattern := by
  change (if pattern.j then d589 (change pattern 10 12) else d588 (change pattern 10 12)) = d2607 pattern
  rw [s3712, s3686]
  rfl
theorem s3714 (pattern : Twelve) : d488 (change pattern 10 12) = d0 pattern := by
  change d0 (change pattern 10 12) = d0 pattern
  exact s3659 pattern
theorem s3715 (pattern : Twelve) : d510 (change pattern 10 12) = d0 pattern := by
  change (if pattern.i then d488 (change pattern 10 12) else d483 (change pattern 10 12)) = d0 pattern
  rw [s3714, s3687]
  simp only [ite_self]
theorem s3716 (pattern : Twelve) : d511 (change pattern 10 12) = d0 pattern := by
  change (if pattern.i then d480 (change pattern 10 12) else d485 (change pattern 10 12)) = d0 pattern
  rw [s3673, s3690]
  simp only [ite_self]
theorem s3717 (pattern : Twelve) : d540 (change pattern 10 12) = d0 pattern := by
  change (if pattern.h then d511 (change pattern 10 12) else d510 (change pattern 10 12)) = d0 pattern
  rw [s3716, s3715]
  simp only [ite_self]
theorem s3718 (pattern : Twelve) : d512 (change pattern 10 12) = d26 pattern := by
  change (if pattern.i then d479 (change pattern 10 12) else d485 (change pattern 10 12)) = d26 pattern
  rw [s3669, s3690]
  rfl
theorem s3719 (pattern : Twelve) : d513 (change pattern 10 12) = d26 pattern := by
  change (if pattern.i then d479 (change pattern 10 12) else d480 (change pattern 10 12)) = d26 pattern
  rw [s3669, s3673]
  rfl
theorem s3720 (pattern : Twelve) : d541 (change pattern 10 12) = d26 pattern := by
  change (if pattern.h then d513 (change pattern 10 12) else d512 (change pattern 10 12)) = d26 pattern
  rw [s3719, s3718]
  simp only [ite_self]
theorem s3721 (pattern : Twelve) : d565 (change pattern 10 12) = d2593 pattern := by
  change (if pattern.f then d541 (change pattern 10 12) else d540 (change pattern 10 12)) = d2593 pattern
  rw [s3720, s3717]
  rfl
theorem s3722 (pattern : Twelve) : d542 (change pattern 10 12) = d0 pattern := by
  change (if pattern.h then d480 (change pattern 10 12) else d511 (change pattern 10 12)) = d0 pattern
  rw [s3673, s3716]
  simp only [ite_self]
theorem s3723 (pattern : Twelve) : d566 (change pattern 10 12) = d2608 pattern := by
  change (if pattern.f then d539 (change pattern 10 12) else d542 (change pattern 10 12)) = d2608 pattern
  rw [s3710, s3722]
  rfl
theorem s3724 (pattern : Twelve) : d590 (change pattern 10 12) = d2609 pattern := by
  change (if pattern.e then d566 (change pattern 10 12) else d565 (change pattern 10 12)) = d2609 pattern
  rw [s3723, s3721]
  rfl
theorem s3725 (pattern : Twelve) : d489 (change pattern 10 12) = d0 pattern := by
  change d0 (change pattern 10 12) = d0 pattern
  exact s3659 pattern
theorem s3726 (pattern : Twelve) : d514 (change pattern 10 12) = d30 pattern := by
  change (if pattern.i then d487 (change pattern 10 12) else d489 (change pattern 10 12)) = d30 pattern
  rw [s3697, s3725]
  rfl
theorem s3727 (pattern : Twelve) : d515 (change pattern 10 12) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 10 12) else d480 (change pattern 10 12)) = d35 pattern
  rw [s3682, s3673]
  rfl
theorem s3728 (pattern : Twelve) : d543 (change pattern 10 12) = d56 pattern := by
  change (if pattern.h then d515 (change pattern 10 12) else d514 (change pattern 10 12)) = d56 pattern
  rw [s3727, s3726]
  rfl
theorem s3729 (pattern : Twelve) : d544 (change pattern 10 12) = d56 pattern := by
  change (if pattern.h then d515 (change pattern 10 12) else d509 (change pattern 10 12)) = d56 pattern
  rw [s3727, s3709]
  rfl
theorem s3730 (pattern : Twelve) : d567 (change pattern 10 12) = d56 pattern := by
  change (if pattern.f then d544 (change pattern 10 12) else d543 (change pattern 10 12)) = d56 pattern
  rw [s3729, s3728]
  simp only [ite_self]
theorem s3731 (pattern : Twelve) : d568 (change pattern 10 12) = d2610 pattern := by
  change (if pattern.f then d539 (change pattern 10 12) else d544 (change pattern 10 12)) = d2610 pattern
  rw [s3710, s3729]
  rfl
theorem s3732 (pattern : Twelve) : d591 (change pattern 10 12) = d2611 pattern := by
  change (if pattern.e then d568 (change pattern 10 12) else d567 (change pattern 10 12)) = d2611 pattern
  rw [s3731, s3730]
  rfl
theorem s3733 (pattern : Twelve) : d607 (change pattern 10 12) = d2612 pattern := by
  change (if pattern.j then d591 (change pattern 10 12) else d590 (change pattern 10 12)) = d2612 pattern
  rw [s3732, s3724]
  rfl
theorem s3734 (pattern : Twelve) : d618 (change pattern 10 12) = d2613 pattern := by
  change (if pattern.d then d607 (change pattern 10 12) else d606 (change pattern 10 12)) = d2613 pattern
  rw [s3733, s3713]
  rfl
theorem s3735 (pattern : Twelve) : d490 (change pattern 10 12) = d0 pattern := by
  change d0 (change pattern 10 12) = d0 pattern
  exact s3659 pattern
theorem s3736 (pattern : Twelve) : d491 (change pattern 10 12) = d2 pattern := by
  change d2 (change pattern 10 12) = d2 pattern
  exact s3676 pattern
theorem s3737 (pattern : Twelve) : d516 (change pattern 10 12) = d30 pattern := by
  change (if pattern.i then d491 (change pattern 10 12) else d490 (change pattern 10 12)) = d30 pattern
  rw [s3736, s3735]
  rfl
theorem s3738 (pattern : Twelve) : d517 (change pattern 10 12) = d30 pattern := by
  change (if pattern.i then d487 (change pattern 10 12) else d488 (change pattern 10 12)) = d30 pattern
  rw [s3697, s3714]
  rfl
theorem s3739 (pattern : Twelve) : d545 (change pattern 10 12) = d30 pattern := by
  change (if pattern.h then d517 (change pattern 10 12) else d516 (change pattern 10 12)) = d30 pattern
  rw [s3738, s3737]
  simp only [ite_self]
theorem s3740 (pattern : Twelve) : d492 (change pattern 10 12) = d3 pattern := by
  change d3 (change pattern 10 12) = d3 pattern
  exact s3691 pattern
theorem s3741 (pattern : Twelve) : d518 (change pattern 10 12) = d123 pattern := by
  change (if pattern.i then d492 (change pattern 10 12) else d480 (change pattern 10 12)) = d123 pattern
  rw [s3740, s3673]
  rfl
theorem s3742 (pattern : Twelve) : d546 (change pattern 10 12) = d132 pattern := by
  change (if pattern.h then d518 (change pattern 10 12) else d517 (change pattern 10 12)) = d132 pattern
  rw [s3741, s3738]
  rfl
theorem s3743 (pattern : Twelve) : d569 (change pattern 10 12) = d2614 pattern := by
  change (if pattern.f then d546 (change pattern 10 12) else d545 (change pattern 10 12)) = d2614 pattern
  rw [s3742, s3739]
  rfl
theorem s3744 (pattern : Twelve) : d547 (change pattern 10 12) = d30 pattern := by
  change (if pattern.h then d509 (change pattern 10 12) else d517 (change pattern 10 12)) = d30 pattern
  rw [s3709, s3738]
  simp only [ite_self]
theorem s3745 (pattern : Twelve) : d570 (change pattern 10 12) = d2615 pattern := by
  change (if pattern.f then d539 (change pattern 10 12) else d547 (change pattern 10 12)) = d2615 pattern
  rw [s3710, s3744]
  rfl
theorem s3746 (pattern : Twelve) : d592 (change pattern 10 12) = d2616 pattern := by
  change (if pattern.e then d570 (change pattern 10 12) else d569 (change pattern 10 12)) = d2616 pattern
  rw [s3745, s3743]
  rfl
theorem s3747 (pattern : Twelve) : d493 (change pattern 10 12) = d2 pattern := by
  change d2 (change pattern 10 12) = d2 pattern
  exact s3676 pattern
theorem s3748 (pattern : Twelve) : d494 (change pattern 10 12) = d4 pattern := by
  change d4 (change pattern 10 12) = d4 pattern
  exact s3699 pattern
theorem s3749 (pattern : Twelve) : d519 (change pattern 10 12) = d38 pattern := by
  change (if pattern.i then d494 (change pattern 10 12) else d493 (change pattern 10 12)) = d38 pattern
  rw [s3748, s3747]
  rfl
end NetHack.Sokoban21.Diagram
