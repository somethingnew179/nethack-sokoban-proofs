/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions24
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s3750 (pattern : Twelve) : d520 (change pattern 10 12) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 10 12) else d487 (change pattern 10 12)) = d39 pattern
  rw [s3682, s3697]
  rfl
theorem s3751 (pattern : Twelve) : d548 (change pattern 10 12) = d59 pattern := by
  change (if pattern.h then d520 (change pattern 10 12) else d519 (change pattern 10 12)) = d59 pattern
  rw [s3750, s3749]
  rfl
theorem s3752 (pattern : Twelve) : d521 (change pattern 10 12) = d38 pattern := by
  change (if pattern.i then d494 (change pattern 10 12) else d487 (change pattern 10 12)) = d38 pattern
  rw [s3748, s3697]
  rfl
theorem s3753 (pattern : Twelve) : d549 (change pattern 10 12) = d59 pattern := by
  change (if pattern.h then d520 (change pattern 10 12) else d521 (change pattern 10 12)) = d59 pattern
  rw [s3750, s3752]
  rfl
theorem s3754 (pattern : Twelve) : d571 (change pattern 10 12) = d59 pattern := by
  change (if pattern.f then d549 (change pattern 10 12) else d548 (change pattern 10 12)) = d59 pattern
  rw [s3753, s3751]
  simp only [ite_self]
theorem s3755 (pattern : Twelve) : d16 (change pattern 10 12) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 10 12) else d2 (change pattern 10 12)) = d16 pattern
  rw [s3699, s3676]
  rfl
theorem s3756 (pattern : Twelve) : d495 (change pattern 10 12) = d16 pattern := by
  change d16 (change pattern 10 12) = d16 pattern
  exact s3755 pattern
theorem s3757 (pattern : Twelve) : d522 (change pattern 10 12) = d2237 pattern := by
  change (if pattern.i then d6 (change pattern 10 12) else d495 (change pattern 10 12)) = d2237 pattern
  rw [s3682, s3756]
  rfl
theorem s3758 (pattern : Twelve) : d550 (change pattern 10 12) = d2617 pattern := by
  change (if pattern.h then d522 (change pattern 10 12) else d521 (change pattern 10 12)) = d2617 pattern
  rw [s3757, s3752]
  rfl
theorem s3759 (pattern : Twelve) : d572 (change pattern 10 12) = d2618 pattern := by
  change (if pattern.f then d550 (change pattern 10 12) else d549 (change pattern 10 12)) = d2618 pattern
  rw [s3758, s3753]
  rfl
theorem s3760 (pattern : Twelve) : d593 (change pattern 10 12) = d2619 pattern := by
  change (if pattern.e then d572 (change pattern 10 12) else d571 (change pattern 10 12)) = d2619 pattern
  rw [s3759, s3754]
  rfl
theorem s3761 (pattern : Twelve) : d608 (change pattern 10 12) = d2620 pattern := by
  change (if pattern.j then d593 (change pattern 10 12) else d592 (change pattern 10 12)) = d2620 pattern
  rw [s3760, s3746]
  rfl
theorem s3762 (pattern : Twelve) : d496 (change pattern 10 12) = d0 pattern := by
  change d0 (change pattern 10 12) = d0 pattern
  exact s3659 pattern
theorem s3763 (pattern : Twelve) : d523 (change pattern 10 12) = d30 pattern := by
  change (if pattern.i then d487 (change pattern 10 12) else d496 (change pattern 10 12)) = d30 pattern
  rw [s3697, s3762]
  rfl
theorem s3764 (pattern : Twelve) : d551 (change pattern 10 12) = d56 pattern := by
  change (if pattern.h then d515 (change pattern 10 12) else d523 (change pattern 10 12)) = d56 pattern
  rw [s3727, s3763]
  rfl
theorem s3765 (pattern : Twelve) : d573 (change pattern 10 12) = d56 pattern := by
  change (if pattern.f then d544 (change pattern 10 12) else d551 (change pattern 10 12)) = d56 pattern
  rw [s3729, s3764]
  simp only [ite_self]
theorem s3766 (pattern : Twelve) : d594 (change pattern 10 12) = d2611 pattern := by
  change (if pattern.e then d568 (change pattern 10 12) else d573 (change pattern 10 12)) = d2611 pattern
  rw [s3731, s3765]
  rfl
theorem s3767 (pattern : Twelve) : d609 (change pattern 10 12) = d2621 pattern := by
  change (if pattern.j then d6 (change pattern 10 12) else d594 (change pattern 10 12)) = d2621 pattern
  rw [s3682, s3766]
  rfl
theorem s3768 (pattern : Twelve) : d619 (change pattern 10 12) = d2622 pattern := by
  change (if pattern.d then d609 (change pattern 10 12) else d608 (change pattern 10 12)) = d2622 pattern
  rw [s3767, s3761]
  rfl
theorem s3769 (pattern : Twelve) : d624 (change pattern 10 12) = d2623 pattern := by
  change (if pattern.c then d619 (change pattern 10 12) else d618 (change pattern 10 12)) = d2623 pattern
  rw [s3768, s3734]
  rfl
theorem s3770 (pattern : Twelve) : d574 (change pattern 10 12) = d2593 pattern := by
  change (if pattern.f then d513 (change pattern 10 12) else d480 (change pattern 10 12)) = d2593 pattern
  rw [s3719, s3673]
  rfl
theorem s3771 (pattern : Twelve) : d524 (change pattern 10 12) = d2594 pattern := by
  change (if pattern.i then d481 (change pattern 10 12) else d480 (change pattern 10 12)) = d2594 pattern
  rw [s3678, s3673]
  rfl
theorem s3772 (pattern : Twelve) : d552 (change pattern 10 12) = d2596 pattern := by
  change (if pattern.h then d503 (change pattern 10 12) else d524 (change pattern 10 12)) = d2596 pattern
  rw [s3683, s3771]
  rfl
theorem s3773 (pattern : Twelve) : d575 (change pattern 10 12) = d2597 pattern := by
  change (if pattern.f then d552 (change pattern 10 12) else d480 (change pattern 10 12)) = d2597 pattern
  rw [s3772, s3673]
  rfl
theorem s3774 (pattern : Twelve) : d595 (change pattern 10 12) = d2598 pattern := by
  change (if pattern.e then d575 (change pattern 10 12) else d574 (change pattern 10 12)) = d2598 pattern
  rw [s3773, s3770]
  rfl
theorem s3775 (pattern : Twelve) : d525 (change pattern 10 12) = d2599 pattern := by
  change (if pattern.i then d486 (change pattern 10 12) else d480 (change pattern 10 12)) = d2599 pattern
  rw [s3694, s3673]
  rfl
theorem s3776 (pattern : Twelve) : d553 (change pattern 10 12) = d2600 pattern := by
  change (if pattern.h then d525 (change pattern 10 12) else d509 (change pattern 10 12)) = d2600 pattern
  rw [s3775, s3709]
  rfl
theorem s3777 (pattern : Twelve) : d554 (change pattern 10 12) = d2066 pattern := by
  change (if pattern.h then d507 (change pattern 10 12) else d509 (change pattern 10 12)) = d2066 pattern
  rw [s3702, s3709]
  rfl
theorem s3778 (pattern : Twelve) : d576 (change pattern 10 12) = d2601 pattern := by
  change (if pattern.f then d554 (change pattern 10 12) else d553 (change pattern 10 12)) = d2601 pattern
  rw [s3777, s3776]
  rfl
theorem s3779 (pattern : Twelve) : d555 (change pattern 10 12) = d2603 pattern := by
  change (if pattern.h then d508 (change pattern 10 12) else d509 (change pattern 10 12)) = d2603 pattern
  rw [s3707, s3709]
  rfl
theorem s3780 (pattern : Twelve) : d577 (change pattern 10 12) = d2605 pattern := by
  change (if pattern.f then d539 (change pattern 10 12) else d555 (change pattern 10 12)) = d2605 pattern
  rw [s3710, s3779]
  rfl
theorem s3781 (pattern : Twelve) : d596 (change pattern 10 12) = d2606 pattern := by
  change (if pattern.e then d577 (change pattern 10 12) else d576 (change pattern 10 12)) = d2606 pattern
  rw [s3780, s3778]
  rfl
theorem s3782 (pattern : Twelve) : d610 (change pattern 10 12) = d2607 pattern := by
  change (if pattern.j then d596 (change pattern 10 12) else d595 (change pattern 10 12)) = d2607 pattern
  rw [s3781, s3774]
  rfl
theorem s3783 (pattern : Twelve) : d578 (change pattern 10 12) = d2608 pattern := by
  change (if pattern.f then d539 (change pattern 10 12) else d480 (change pattern 10 12)) = d2608 pattern
  rw [s3710, s3673]
  rfl
theorem s3784 (pattern : Twelve) : d597 (change pattern 10 12) = d2609 pattern := by
  change (if pattern.e then d578 (change pattern 10 12) else d574 (change pattern 10 12)) = d2609 pattern
  rw [s3783, s3770]
  rfl
theorem s3785 (pattern : Twelve) : d598 (change pattern 10 12) = d2611 pattern := by
  change (if pattern.e then d568 (change pattern 10 12) else d544 (change pattern 10 12)) = d2611 pattern
  rw [s3731, s3729]
  rfl
theorem s3786 (pattern : Twelve) : d611 (change pattern 10 12) = d2612 pattern := by
  change (if pattern.j then d598 (change pattern 10 12) else d597 (change pattern 10 12)) = d2612 pattern
  rw [s3785, s3784]
  rfl
theorem s3787 (pattern : Twelve) : d620 (change pattern 10 12) = d2613 pattern := by
  change (if pattern.d then d611 (change pattern 10 12) else d610 (change pattern 10 12)) = d2613 pattern
  rw [s3786, s3782]
  rfl
theorem s3788 (pattern : Twelve) : d556 (change pattern 10 12) = d132 pattern := by
  change (if pattern.h then d518 (change pattern 10 12) else d509 (change pattern 10 12)) = d132 pattern
  rw [s3741, s3709]
  rfl
theorem s3789 (pattern : Twelve) : d579 (change pattern 10 12) = d2614 pattern := by
  change (if pattern.f then d556 (change pattern 10 12) else d509 (change pattern 10 12)) = d2614 pattern
  rw [s3788, s3709]
  rfl
theorem s3790 (pattern : Twelve) : d580 (change pattern 10 12) = d2615 pattern := by
  change (if pattern.f then d539 (change pattern 10 12) else d509 (change pattern 10 12)) = d2615 pattern
  rw [s3710, s3709]
  rfl
theorem s3791 (pattern : Twelve) : d599 (change pattern 10 12) = d2616 pattern := by
  change (if pattern.e then d580 (change pattern 10 12) else d579 (change pattern 10 12)) = d2616 pattern
  rw [s3790, s3789]
  rfl
theorem s3792 (pattern : Twelve) : d600 (change pattern 10 12) = d2619 pattern := by
  change (if pattern.e then d572 (change pattern 10 12) else d549 (change pattern 10 12)) = d2619 pattern
  rw [s3759, s3753]
  rfl
theorem s3793 (pattern : Twelve) : d612 (change pattern 10 12) = d2620 pattern := by
  change (if pattern.j then d600 (change pattern 10 12) else d599 (change pattern 10 12)) = d2620 pattern
  rw [s3792, s3791]
  rfl
theorem s3794 (pattern : Twelve) : d613 (change pattern 10 12) = d2621 pattern := by
  change (if pattern.j then d6 (change pattern 10 12) else d598 (change pattern 10 12)) = d2621 pattern
  rw [s3682, s3785]
  rfl
theorem s3795 (pattern : Twelve) : d621 (change pattern 10 12) = d2622 pattern := by
  change (if pattern.d then d613 (change pattern 10 12) else d612 (change pattern 10 12)) = d2622 pattern
  rw [s3794, s3793]
  rfl
theorem s3796 (pattern : Twelve) : d625 (change pattern 10 12) = d2623 pattern := by
  change (if pattern.c then d621 (change pattern 10 12) else d620 (change pattern 10 12)) = d2623 pattern
  rw [s3795, s3787]
  rfl
theorem s3797 (pattern : Twelve) : d627 (change pattern 10 12) = d2623 pattern := by
  change (if pattern.g then d625 (change pattern 10 12) else d624 (change pattern 10 12)) = d2623 pattern
  rw [s3796, s3769]
  simp only [ite_self]
theorem s3798 (pattern : Twelve) : d628 (change pattern 10 12) = d2623 pattern := by
  change (if pattern.b then d625 (change pattern 10 12) else d627 (change pattern 10 12)) = d2623 pattern
  rw [s3796, s3797]
  simp only [ite_self]
theorem s3799 (pattern : Twelve) : d526 (change pattern 10 12) = d2624 pattern := by
  change (if pattern.i then d495 (change pattern 10 12) else d480 (change pattern 10 12)) = d2624 pattern
  rw [s3756, s3673]
  rfl
theorem s3800 (pattern : Twelve) : d557 (change pattern 10 12) = d2625 pattern := by
  change (if pattern.h then d503 (change pattern 10 12) else d526 (change pattern 10 12)) = d2625 pattern
  rw [s3683, s3799]
  rfl
theorem s3801 (pattern : Twelve) : d581 (change pattern 10 12) = d2626 pattern := by
  change (if pattern.f then d557 (change pattern 10 12) else d480 (change pattern 10 12)) = d2626 pattern
  rw [s3800, s3673]
  rfl
theorem s3802 (pattern : Twelve) : d601 (change pattern 10 12) = d2627 pattern := by
  change (if pattern.e then d581 (change pattern 10 12) else d574 (change pattern 10 12)) = d2627 pattern
  rw [s3801, s3770]
  rfl
theorem s3803 (pattern : Twelve) : d582 (change pattern 10 12) = d2628 pattern := by
  change (if pattern.f then d544 (change pattern 10 12) else d553 (change pattern 10 12)) = d2628 pattern
  rw [s3729, s3776]
  rfl
theorem s3804 (pattern : Twelve) : d583 (change pattern 10 12) = d2629 pattern := by
  change (if pattern.f then d557 (change pattern 10 12) else d544 (change pattern 10 12)) = d2629 pattern
  rw [s3800, s3729]
  rfl
theorem s3805 (pattern : Twelve) : d602 (change pattern 10 12) = d2630 pattern := by
  change (if pattern.e then d583 (change pattern 10 12) else d582 (change pattern 10 12)) = d2630 pattern
  rw [s3804, s3803]
  rfl
theorem s3806 (pattern : Twelve) : d614 (change pattern 10 12) = d2631 pattern := by
  change (if pattern.j then d602 (change pattern 10 12) else d601 (change pattern 10 12)) = d2631 pattern
  rw [s3805, s3802]
  rfl
theorem s3807 (pattern : Twelve) : d603 (change pattern 10 12) = d2632 pattern := by
  change (if pattern.e then d583 (change pattern 10 12) else d544 (change pattern 10 12)) = d2632 pattern
  rw [s3804, s3729]
  rfl
theorem s3808 (pattern : Twelve) : d615 (change pattern 10 12) = d2633 pattern := by
  change (if pattern.j then d603 (change pattern 10 12) else d601 (change pattern 10 12)) = d2633 pattern
  rw [s3807, s3802]
  rfl
theorem s3809 (pattern : Twelve) : d622 (change pattern 10 12) = d2634 pattern := by
  change (if pattern.d then d615 (change pattern 10 12) else d614 (change pattern 10 12)) = d2634 pattern
  rw [s3808, s3806]
  rfl
theorem s3810 (pattern : Twelve) : d527 (change pattern 10 12) = d2635 pattern := by
  change (if pattern.i then d494 (change pattern 10 12) else d480 (change pattern 10 12)) = d2635 pattern
  rw [s3748, s3673]
  rfl
theorem s3811 (pattern : Twelve) : d558 (change pattern 10 12) = d2636 pattern := by
  change (if pattern.h then d527 (change pattern 10 12) else d509 (change pattern 10 12)) = d2636 pattern
  rw [s3810, s3709]
  rfl
theorem s3812 (pattern : Twelve) : d584 (change pattern 10 12) = d2637 pattern := by
  change (if pattern.f then d558 (change pattern 10 12) else d509 (change pattern 10 12)) = d2637 pattern
  rw [s3811, s3709]
  rfl
theorem s3813 (pattern : Twelve) : d585 (change pattern 10 12) = d2638 pattern := by
  change (if pattern.f then d557 (change pattern 10 12) else d556 (change pattern 10 12)) = d2638 pattern
  rw [s3800, s3788]
  rfl
theorem s3814 (pattern : Twelve) : d604 (change pattern 10 12) = d2639 pattern := by
  change (if pattern.e then d585 (change pattern 10 12) else d584 (change pattern 10 12)) = d2639 pattern
  rw [s3813, s3812]
  rfl
theorem s3815 (pattern : Twelve) : d497 (change pattern 10 12) = d5 pattern := by
  change d5 (change pattern 10 12) = d5 pattern
  exact s3692 pattern
theorem s3816 (pattern : Twelve) : d528 (change pattern 10 12) = d126 pattern := by
  change (if pattern.i then d497 (change pattern 10 12) else d487 (change pattern 10 12)) = d126 pattern
  rw [s3815, s3697]
  rfl
theorem s3817 (pattern : Twelve) : d529 (change pattern 10 12) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 10 12) else d492 (change pattern 10 12)) = d47 pattern
  rw [s3682, s3740]
  rfl
theorem s3818 (pattern : Twelve) : d559 (change pattern 10 12) = d134 pattern := by
  change (if pattern.h then d529 (change pattern 10 12) else d528 (change pattern 10 12)) = d134 pattern
  rw [s3817, s3816]
  rfl
theorem s3819 (pattern : Twelve) : d586 (change pattern 10 12) = d2640 pattern := by
  change (if pattern.f then d559 (change pattern 10 12) else d549 (change pattern 10 12)) = d2640 pattern
  rw [s3818, s3753]
  rfl
theorem s3820 (pattern : Twelve) : d530 (change pattern 10 12) = d2115 pattern := by
  change (if pattern.i then d22 (change pattern 10 12) else d487 (change pattern 10 12)) = d2115 pattern
  rw [s3706, s3697]
  rfl
theorem s3821 (pattern : Twelve) : d531 (change pattern 10 12) = d2088 pattern := by
  change (if pattern.i then d6 (change pattern 10 12) else d486 (change pattern 10 12)) = d2088 pattern
  rw [s3682, s3694]
  rfl
theorem s3822 (pattern : Twelve) : d560 (change pattern 10 12) = d2641 pattern := by
  change (if pattern.h then d531 (change pattern 10 12) else d530 (change pattern 10 12)) = d2641 pattern
  rw [s3821, s3820]
  rfl
theorem s3823 (pattern : Twelve) : d587 (change pattern 10 12) = d2642 pattern := by
  change (if pattern.f then d560 (change pattern 10 12) else d559 (change pattern 10 12)) = d2642 pattern
  rw [s3822, s3818]
  rfl
theorem s3824 (pattern : Twelve) : d605 (change pattern 10 12) = d2643 pattern := by
  change (if pattern.e then d587 (change pattern 10 12) else d586 (change pattern 10 12)) = d2643 pattern
  rw [s3823, s3819]
  rfl
theorem s3825 (pattern : Twelve) : d616 (change pattern 10 12) = d2644 pattern := by
  change (if pattern.j then d605 (change pattern 10 12) else d604 (change pattern 10 12)) = d2644 pattern
  rw [s3824, s3814]
  rfl
theorem s3826 (pattern : Twelve) : d617 (change pattern 10 12) = d2645 pattern := by
  change (if pattern.j then d6 (change pattern 10 12) else d603 (change pattern 10 12)) = d2645 pattern
  rw [s3682, s3807]
  rfl
theorem s3827 (pattern : Twelve) : d623 (change pattern 10 12) = d2646 pattern := by
  change (if pattern.d then d617 (change pattern 10 12) else d616 (change pattern 10 12)) = d2646 pattern
  rw [s3826, s3825]
  rfl
theorem s3828 (pattern : Twelve) : d626 (change pattern 10 12) = d2647 pattern := by
  change (if pattern.c then d623 (change pattern 10 12) else d622 (change pattern 10 12)) = d2647 pattern
  rw [s3827, s3809]
  rfl
theorem s3829 (pattern : Twelve) : d629 (change pattern 10 12) = d2648 pattern := by
  change (if pattern.a then d626 (change pattern 10 12) else d628 (change pattern 10 12)) = d2648 pattern
  rw [s3828, s3798]
  rfl
theorem s3830 (pattern : Twelve) : d7 (change pattern 10 12) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 10 12) else d0 (change pattern 10 12)) = d7 pattern
  rw [s3665, s3659]
  rfl
theorem s3831 (pattern : Twelve) : d1105 (change pattern 10 12) = d7 pattern := by
  change d7 (change pattern 10 12) = d7 pattern
  exact s3830 pattern
theorem s3832 (pattern : Twelve) : d1108 (change pattern 10 12) = d2057 pattern := by
  change (if pattern.i then d479 (change pattern 10 12) else d1105 (change pattern 10 12)) = d2057 pattern
  rw [s3669, s3831]
  rfl
theorem s3833 (pattern : Twelve) : d1118 (change pattern 10 12) = d2058 pattern := by
  change (if pattern.h then d1108 (change pattern 10 12) else d500 (change pattern 10 12)) = d2058 pattern
  rw [s3832, s3670]
  rfl
theorem s3834 (pattern : Twelve) : d1132 (change pattern 10 12) = d2059 pattern := by
  change (if pattern.f then d1118 (change pattern 10 12) else d534 (change pattern 10 12)) = d2059 pattern
  rw [s3833, s3675]
  rfl
theorem s3835 (pattern : Twelve) : d1119 (change pattern 10 12) = d0 pattern := by
  change (if pattern.h then d480 (change pattern 10 12) else d501 (change pattern 10 12)) = d0 pattern
  rw [s3673, s3674]
  simp only [ite_self]
theorem s3836 (pattern : Twelve) : d1109 (change pattern 10 12) = d2649 pattern := by
  change (if pattern.i then d495 (change pattern 10 12) else d482 (change pattern 10 12)) = d2649 pattern
  rw [s3756, s3681]
  rfl
theorem s3837 (pattern : Twelve) : d1120 (change pattern 10 12) = d2650 pattern := by
  change (if pattern.h then d522 (change pattern 10 12) else d1109 (change pattern 10 12)) = d2650 pattern
  rw [s3757, s3836]
  rfl
theorem s3838 (pattern : Twelve) : d1133 (change pattern 10 12) = d2651 pattern := by
  change (if pattern.f then d1120 (change pattern 10 12) else d1119 (change pattern 10 12)) = d2651 pattern
  rw [s3837, s3835]
  rfl
theorem s3839 (pattern : Twelve) : d1152 (change pattern 10 12) = d2652 pattern := by
  change (if pattern.e then d1133 (change pattern 10 12) else d1132 (change pattern 10 12)) = d2652 pattern
  rw [s3838, s3834]
  rfl
theorem s3840 (pattern : Twelve) : d1121 (change pattern 10 12) = d56 pattern := by
  change (if pattern.h then d515 (change pattern 10 12) else d506 (change pattern 10 12)) = d56 pattern
  rw [s3727, s3698]
  rfl
theorem s3841 (pattern : Twelve) : d1110 (change pattern 10 12) = d2073 pattern := by
  change (if pattern.i then d6 (change pattern 10 12) else d1105 (change pattern 10 12)) = d2073 pattern
  rw [s3682, s3831]
  rfl
theorem s3842 (pattern : Twelve) : d1122 (change pattern 10 12) = d2074 pattern := by
  change (if pattern.h then d1110 (change pattern 10 12) else d509 (change pattern 10 12)) = d2074 pattern
  rw [s3841, s3709]
  rfl
theorem s3843 (pattern : Twelve) : d1134 (change pattern 10 12) = d2075 pattern := by
  change (if pattern.f then d1122 (change pattern 10 12) else d1121 (change pattern 10 12)) = d2075 pattern
  rw [s3842, s3840]
  rfl
theorem s3844 (pattern : Twelve) : d1135 (change pattern 10 12) = d2653 pattern := by
  change (if pattern.f then d1120 (change pattern 10 12) else d544 (change pattern 10 12)) = d2653 pattern
  rw [s3837, s3729]
  rfl
theorem s3845 (pattern : Twelve) : d1153 (change pattern 10 12) = d2654 pattern := by
  change (if pattern.e then d1135 (change pattern 10 12) else d1134 (change pattern 10 12)) = d2654 pattern
  rw [s3844, s3843]
  rfl
theorem s3846 (pattern : Twelve) : d1164 (change pattern 10 12) = d2655 pattern := by
  change (if pattern.j then d1153 (change pattern 10 12) else d1152 (change pattern 10 12)) = d2655 pattern
  rw [s3845, s3839]
  rfl
theorem s3847 (pattern : Twelve) : d1123 (change pattern 10 12) = d2058 pattern := by
  change (if pattern.h then d1108 (change pattern 10 12) else d513 (change pattern 10 12)) = d2058 pattern
  rw [s3832, s3719]
  rfl
theorem s3848 (pattern : Twelve) : d1136 (change pattern 10 12) = d2059 pattern := by
  change (if pattern.f then d1123 (change pattern 10 12) else d542 (change pattern 10 12)) = d2059 pattern
  rw [s3847, s3722]
  rfl
theorem s3849 (pattern : Twelve) : d1137 (change pattern 10 12) = d2651 pattern := by
  change (if pattern.f then d1120 (change pattern 10 12) else d480 (change pattern 10 12)) = d2651 pattern
  rw [s3837, s3673]
  rfl
theorem s3850 (pattern : Twelve) : d1154 (change pattern 10 12) = d2652 pattern := by
  change (if pattern.e then d1137 (change pattern 10 12) else d1136 (change pattern 10 12)) = d2652 pattern
  rw [s3849, s3848]
  rfl
theorem s3851 (pattern : Twelve) : d1138 (change pattern 10 12) = d2075 pattern := by
  change (if pattern.f then d1122 (change pattern 10 12) else d544 (change pattern 10 12)) = d2075 pattern
  rw [s3842, s3729]
  rfl
theorem s3852 (pattern : Twelve) : d1155 (change pattern 10 12) = d2654 pattern := by
  change (if pattern.e then d1135 (change pattern 10 12) else d1138 (change pattern 10 12)) = d2654 pattern
  rw [s3844, s3851]
  rfl
theorem s3853 (pattern : Twelve) : d1165 (change pattern 10 12) = d2655 pattern := by
  change (if pattern.j then d1155 (change pattern 10 12) else d1154 (change pattern 10 12)) = d2655 pattern
  rw [s3852, s3850]
  rfl
theorem s3854 (pattern : Twelve) : d1173 (change pattern 10 12) = d2655 pattern := by
  change (if pattern.d then d1165 (change pattern 10 12) else d1164 (change pattern 10 12)) = d2655 pattern
  rw [s3853, s3846]
  simp only [ite_self]
theorem s3855 (pattern : Twelve) : d1111 (change pattern 10 12) = d2079 pattern := by
  change (if pattern.i then d492 (change pattern 10 12) else d1105 (change pattern 10 12)) = d2079 pattern
  rw [s3740, s3831]
  rfl
theorem s3856 (pattern : Twelve) : d1124 (change pattern 10 12) = d2080 pattern := by
  change (if pattern.h then d1111 (change pattern 10 12) else d509 (change pattern 10 12)) = d2080 pattern
  rw [s3855, s3709]
  rfl
theorem s3857 (pattern : Twelve) : d1139 (change pattern 10 12) = d2081 pattern := by
  change (if pattern.f then d1124 (change pattern 10 12) else d547 (change pattern 10 12)) = d2081 pattern
  rw [s3856, s3744]
  rfl
theorem s3858 (pattern : Twelve) : d1140 (change pattern 10 12) = d2656 pattern := by
  change (if pattern.f then d1120 (change pattern 10 12) else d509 (change pattern 10 12)) = d2656 pattern
  rw [s3837, s3709]
  rfl
theorem s3859 (pattern : Twelve) : d1156 (change pattern 10 12) = d2657 pattern := by
  change (if pattern.e then d1140 (change pattern 10 12) else d1139 (change pattern 10 12)) = d2657 pattern
  rw [s3858, s3857]
  rfl
theorem s3860 (pattern : Twelve) : d9 (change pattern 10 12) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 10 12) else d2 (change pattern 10 12)) = d9 pattern
  rw [s3691, s3676]
  rfl
theorem s3861 (pattern : Twelve) : d1106 (change pattern 10 12) = d9 pattern := by
  change d9 (change pattern 10 12) = d9 pattern
  exact s3860 pattern
theorem s3862 (pattern : Twelve) : d1112 (change pattern 10 12) = d2084 pattern := by
  change (if pattern.i then d6 (change pattern 10 12) else d1106 (change pattern 10 12)) = d2084 pattern
  rw [s3682, s3861]
  rfl
theorem s3863 (pattern : Twelve) : d1125 (change pattern 10 12) = d2085 pattern := by
  change (if pattern.h then d1112 (change pattern 10 12) else d521 (change pattern 10 12)) = d2085 pattern
  rw [s3862, s3752]
  rfl
theorem s3864 (pattern : Twelve) : d1141 (change pattern 10 12) = d2086 pattern := by
  change (if pattern.f then d1125 (change pattern 10 12) else d549 (change pattern 10 12)) = d2086 pattern
  rw [s3863, s3753]
  rfl
theorem s3865 (pattern : Twelve) : d1113 (change pattern 10 12) = d2236 pattern := by
  change (if pattern.i then d170 (change pattern 10 12) else d495 (change pattern 10 12)) = d2236 pattern
  rw [s3701, s3756]
  rfl
theorem s3866 (pattern : Twelve) : d178 (change pattern 10 12) = d2119 pattern := by
  change (if pattern.i then d6 (change pattern 10 12) else d170 (change pattern 10 12)) = d2119 pattern
  rw [s3682, s3701]
  rfl
theorem s3867 (pattern : Twelve) : d1126 (change pattern 10 12) = d2658 pattern := by
  change (if pattern.h then d178 (change pattern 10 12) else d1113 (change pattern 10 12)) = d2658 pattern
  rw [s3866, s3865]
  rfl
theorem s3868 (pattern : Twelve) : d1142 (change pattern 10 12) = d2659 pattern := by
  change (if pattern.f then d1126 (change pattern 10 12) else d549 (change pattern 10 12)) = d2659 pattern
  rw [s3867, s3753]
  rfl
theorem s3869 (pattern : Twelve) : d1157 (change pattern 10 12) = d2660 pattern := by
  change (if pattern.e then d1142 (change pattern 10 12) else d1141 (change pattern 10 12)) = d2660 pattern
  rw [s3868, s3864]
  rfl
theorem s3870 (pattern : Twelve) : d1166 (change pattern 10 12) = d2661 pattern := by
  change (if pattern.j then d1157 (change pattern 10 12) else d1156 (change pattern 10 12)) = d2661 pattern
  rw [s3869, s3859]
  rfl
theorem s3871 (pattern : Twelve) : d1167 (change pattern 10 12) = d2662 pattern := by
  change (if pattern.j then d6 (change pattern 10 12) else d1155 (change pattern 10 12)) = d2662 pattern
  rw [s3682, s3852]
  rfl
theorem s3872 (pattern : Twelve) : d1174 (change pattern 10 12) = d2663 pattern := by
  change (if pattern.d then d1167 (change pattern 10 12) else d1166 (change pattern 10 12)) = d2663 pattern
  rw [s3871, s3870]
  rfl
theorem s3873 (pattern : Twelve) : d1177 (change pattern 10 12) = d2664 pattern := by
  change (if pattern.c then d1174 (change pattern 10 12) else d1173 (change pattern 10 12)) = d2664 pattern
  rw [s3872, s3854]
  rfl
theorem s3874 (pattern : Twelve) : d1143 (change pattern 10 12) = d2059 pattern := by
  change (if pattern.f then d1123 (change pattern 10 12) else d480 (change pattern 10 12)) = d2059 pattern
  rw [s3847, s3673]
  rfl
theorem s3875 (pattern : Twelve) : d1158 (change pattern 10 12) = d2652 pattern := by
  change (if pattern.e then d1137 (change pattern 10 12) else d1143 (change pattern 10 12)) = d2652 pattern
  rw [s3849, s3874]
  rfl
theorem s3876 (pattern : Twelve) : d1168 (change pattern 10 12) = d2655 pattern := by
  change (if pattern.j then d1155 (change pattern 10 12) else d1158 (change pattern 10 12)) = d2655 pattern
  rw [s3852, s3875]
  rfl
theorem s3877 (pattern : Twelve) : d1144 (change pattern 10 12) = d2081 pattern := by
  change (if pattern.f then d1124 (change pattern 10 12) else d509 (change pattern 10 12)) = d2081 pattern
  rw [s3856, s3709]
  rfl
theorem s3878 (pattern : Twelve) : d1159 (change pattern 10 12) = d2657 pattern := by
  change (if pattern.e then d1140 (change pattern 10 12) else d1144 (change pattern 10 12)) = d2657 pattern
  rw [s3858, s3877]
  rfl
theorem s3879 (pattern : Twelve) : d1169 (change pattern 10 12) = d2661 pattern := by
  change (if pattern.j then d1157 (change pattern 10 12) else d1159 (change pattern 10 12)) = d2661 pattern
  rw [s3869, s3878]
  rfl
theorem s3880 (pattern : Twelve) : d1175 (change pattern 10 12) = d2663 pattern := by
  change (if pattern.d then d1167 (change pattern 10 12) else d1169 (change pattern 10 12)) = d2663 pattern
  rw [s3871, s3879]
  rfl
theorem s3881 (pattern : Twelve) : d1178 (change pattern 10 12) = d2664 pattern := by
  change (if pattern.c then d1175 (change pattern 10 12) else d1168 (change pattern 10 12)) = d2664 pattern
  rw [s3880, s3876]
  rfl
theorem s3882 (pattern : Twelve) : d1180 (change pattern 10 12) = d2664 pattern := by
  change (if pattern.g then d1178 (change pattern 10 12) else d1177 (change pattern 10 12)) = d2664 pattern
  rw [s3881, s3873]
  simp only [ite_self]
theorem s3883 (pattern : Twelve) : d1181 (change pattern 10 12) = d2664 pattern := by
  change (if pattern.b then d1178 (change pattern 10 12) else d1180 (change pattern 10 12)) = d2664 pattern
  rw [s3881, s3882]
  simp only [ite_self]
theorem s3884 (pattern : Twelve) : d1114 (change pattern 10 12) = d2665 pattern := by
  change (if pattern.i then d170 (change pattern 10 12) else d482 (change pattern 10 12)) = d2665 pattern
  rw [s3701, s3681]
  rfl
theorem s3885 (pattern : Twelve) : d1127 (change pattern 10 12) = d2666 pattern := by
  change (if pattern.h then d522 (change pattern 10 12) else d1114 (change pattern 10 12)) = d2666 pattern
  rw [s3757, s3884]
  rfl
theorem s3886 (pattern : Twelve) : d1145 (change pattern 10 12) = d2667 pattern := by
  change (if pattern.f then d1127 (change pattern 10 12) else d480 (change pattern 10 12)) = d2667 pattern
  rw [s3885, s3673]
  rfl
theorem s3887 (pattern : Twelve) : d1160 (change pattern 10 12) = d2668 pattern := by
  change (if pattern.e then d1145 (change pattern 10 12) else d1143 (change pattern 10 12)) = d2668 pattern
  rw [s3886, s3874]
  rfl
theorem s3888 (pattern : Twelve) : d1115 (change pattern 10 12) = d2100 pattern := by
  change (if pattern.i then d1106 (change pattern 10 12) else d480 (change pattern 10 12)) = d2100 pattern
  rw [s3861, s3673]
  rfl
theorem s3889 (pattern : Twelve) : d1128 (change pattern 10 12) = d2101 pattern := by
  change (if pattern.h then d1110 (change pattern 10 12) else d1115 (change pattern 10 12)) = d2101 pattern
  rw [s3841, s3888]
  rfl
theorem s3890 (pattern : Twelve) : d1146 (change pattern 10 12) = d2106 pattern := by
  change (if pattern.f then d1128 (change pattern 10 12) else d544 (change pattern 10 12)) = d2106 pattern
  rw [s3889, s3729]
  rfl
theorem s3891 (pattern : Twelve) : d1147 (change pattern 10 12) = d2669 pattern := by
  change (if pattern.f then d1127 (change pattern 10 12) else d544 (change pattern 10 12)) = d2669 pattern
  rw [s3885, s3729]
  rfl
theorem s3892 (pattern : Twelve) : d1161 (change pattern 10 12) = d2670 pattern := by
  change (if pattern.e then d1147 (change pattern 10 12) else d1146 (change pattern 10 12)) = d2670 pattern
  rw [s3891, s3890]
  rfl
theorem s3893 (pattern : Twelve) : d1170 (change pattern 10 12) = d2671 pattern := by
  change (if pattern.j then d1161 (change pattern 10 12) else d1160 (change pattern 10 12)) = d2671 pattern
  rw [s3892, s3887]
  rfl
theorem s3894 (pattern : Twelve) : d1116 (change pattern 10 12) = d2110 pattern := by
  change (if pattern.i then d494 (change pattern 10 12) else d1105 (change pattern 10 12)) = d2110 pattern
  rw [s3748, s3831]
  rfl
theorem s3895 (pattern : Twelve) : d1129 (change pattern 10 12) = d2111 pattern := by
  change (if pattern.h then d1116 (change pattern 10 12) else d1115 (change pattern 10 12)) = d2111 pattern
  rw [s3894, s3888]
  rfl
theorem s3896 (pattern : Twelve) : d1148 (change pattern 10 12) = d2112 pattern := by
  change (if pattern.f then d1129 (change pattern 10 12) else d509 (change pattern 10 12)) = d2112 pattern
  rw [s3895, s3709]
  rfl
theorem s3897 (pattern : Twelve) : d1149 (change pattern 10 12) = d2672 pattern := by
  change (if pattern.f then d1127 (change pattern 10 12) else d556 (change pattern 10 12)) = d2672 pattern
  rw [s3885, s3788]
  rfl
theorem s3898 (pattern : Twelve) : d1162 (change pattern 10 12) = d2673 pattern := by
  change (if pattern.e then d1149 (change pattern 10 12) else d1148 (change pattern 10 12)) = d2673 pattern
  rw [s3897, s3896]
  rfl
theorem s3899 (pattern : Twelve) : d117 (change pattern 10 12) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 10 12) else d3 (change pattern 10 12)) = d117 pattern
  rw [s3699, s3691]
  rfl
end NetHack.Sokoban21.Diagram
