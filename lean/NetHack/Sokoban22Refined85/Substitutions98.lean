/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions97
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub11760 (p : Pattern) : d3545 (change p 247 none) = d6561 p := by
  change (if p 224 then d3543 (change p 247 none) else d3544 (change p 247 none)) = d6561 p
  rw [sub11758, sub11759]
  rfl
theorem sub11761 (p : Pattern) : d3546 (change p 247 none) = d6562 p := by
  change (if p 204 then d3545 (change p 247 none) else d3542 (change p 247 none)) = d6562 p
  rw [sub11760, sub11755]
  rfl
theorem sub11762 (p : Pattern) : d2 (change p 247 none) = d2 p := by
  rfl
theorem sub11763 (p : Pattern) : d30 (change p 247 none) = d2 p := by
  change d2 (change p 247 none) = d2 p
  exact sub11762 p
theorem sub11764 (p : Pattern) : d3547 (change p 247 none) = d6563 p := by
  change (if p 246 then d30 (change p 247 none) else d13 (change p 247 none)) = d6563 p
  rw [sub11763, sub11752]
  rfl
theorem sub11765 (p : Pattern) : d3548 (change p 247 none) = d6564 p := by
  change (if p 225 then d3547 (change p 247 none) else d13 (change p 247 none)) = d6564 p
  rw [sub11764, sub11752]
  rfl
theorem sub11766 (p : Pattern) : d3549 (change p 247 none) = d6565 p := by
  change (if p 224 then d3547 (change p 247 none) else d3548 (change p 247 none)) = d6565 p
  rw [sub11764, sub11765]
  rfl
theorem sub11767 (p : Pattern) : d12 (change p 247 none) = d12 p := by
  rfl
theorem sub11768 (p : Pattern) : d3550 (change p 247 none) = d6566 p := by
  change (if p 204 then d12 (change p 247 none) else d3549 (change p 247 none)) = d6566 p
  rw [sub11767, sub11766]
  rfl
theorem sub11769 (p : Pattern) : d3551 (change p 247 none) = d6567 p := by
  change (if p 182 then d3550 (change p 247 none) else d3546 (change p 247 none)) = d6567 p
  rw [sub11768, sub11761]
  rfl
theorem sub11770 (p : Pattern) : d3552 (change p 247 none) = d6562 p := by
  change (if p 204 then d3545 (change p 247 none) else d13 (change p 247 none)) = d6562 p
  rw [sub11760, sub11752]
  rfl
theorem sub11771 (p : Pattern) : d3553 (change p 247 none) = d6567 p := by
  change (if p 182 then d3550 (change p 247 none) else d3552 (change p 247 none)) = d6567 p
  rw [sub11768, sub11770]
  rfl
theorem sub11772 (p : Pattern) : d3554 (change p 247 none) = d6567 p := by
  change (if p 163 then d3553 (change p 247 none) else d3551 (change p 247 none)) = d6567 p
  rw [sub11771, sub11769]
  simp only [ite_self]
theorem sub11773 (p : Pattern) : d8 (change p 247 none) = d8 p := by
  rfl
theorem sub11774 (p : Pattern) : d190 (change p 247 none) = d8 p := by
  change d8 (change p 247 none) = d8 p
  exact sub11773 p
theorem sub11775 (p : Pattern) : d3555 (change p 247 none) = d6568 p := by
  change (if p 246 then d190 (change p 247 none) else d17 (change p 247 none)) = d6568 p
  rw [sub11774, sub11757]
  rfl
theorem sub11776 (p : Pattern) : d3556 (change p 247 none) = d6569 p := by
  change (if p 225 then d3555 (change p 247 none) else d17 (change p 247 none)) = d6569 p
  rw [sub11775, sub11757]
  rfl
theorem sub11777 (p : Pattern) : d3557 (change p 247 none) = d6570 p := by
  change (if p 224 then d3555 (change p 247 none) else d3556 (change p 247 none)) = d6570 p
  rw [sub11775, sub11776]
  rfl
theorem sub11778 (p : Pattern) : d3558 (change p 247 none) = d6571 p := by
  change (if p 204 then d3557 (change p 247 none) else d17 (change p 247 none)) = d6571 p
  rw [sub11777, sub11757]
  rfl
theorem sub11779 (p : Pattern) : d6 (change p 247 none) = d6 p := by
  rfl
theorem sub11780 (p : Pattern) : d34 (change p 247 none) = d6 p := by
  change d6 (change p 247 none) = d6 p
  exact sub11779 p
theorem sub11781 (p : Pattern) : d3559 (change p 247 none) = d6572 p := by
  change (if p 246 then d34 (change p 247 none) else d17 (change p 247 none)) = d6572 p
  rw [sub11780, sub11757]
  rfl
theorem sub11782 (p : Pattern) : d3560 (change p 247 none) = d6573 p := by
  change (if p 225 then d3559 (change p 247 none) else d17 (change p 247 none)) = d6573 p
  rw [sub11781, sub11757]
  rfl
theorem sub11783 (p : Pattern) : d3561 (change p 247 none) = d6574 p := by
  change (if p 224 then d3559 (change p 247 none) else d3560 (change p 247 none)) = d6574 p
  rw [sub11781, sub11782]
  rfl
theorem sub11784 (p : Pattern) : d3562 (change p 247 none) = d6575 p := by
  change (if p 204 then d12 (change p 247 none) else d3561 (change p 247 none)) = d6575 p
  rw [sub11767, sub11783]
  rfl
theorem sub11785 (p : Pattern) : d3563 (change p 247 none) = d6576 p := by
  change (if p 182 then d3562 (change p 247 none) else d3558 (change p 247 none)) = d6576 p
  rw [sub11784, sub11778]
  rfl
theorem sub11786 (p : Pattern) : d3564 (change p 247 none) = d6577 p := by
  change (if p 163 then d3563 (change p 247 none) else d3553 (change p 247 none)) = d6577 p
  rw [sub11785, sub11771]
  rfl
theorem sub11787 (p : Pattern) : d3565 (change p 247 none) = d6578 p := by
  change (if p 162 then d3564 (change p 247 none) else d3554 (change p 247 none)) = d6578 p
  rw [sub11786, sub11772]
  rfl
theorem sub11788 (p : Pattern) : d9 (change p 247 none) = d9 p := by
  rfl
theorem sub11789 (p : Pattern) : d23 (change p 247 none) = d9 p := by
  change d9 (change p 247 none) = d9 p
  exact sub11788 p
theorem sub11790 (p : Pattern) : d356 (change p 247 none) = d3244 p := by
  change (if p 246 then d12 (change p 247 none) else d23 (change p 247 none)) = d3244 p
  rw [sub11767, sub11789]
  rfl
theorem sub11791 (p : Pattern) : d3566 (change p 247 none) = d6579 p := by
  change (if p 225 then d356 (change p 247 none) else d23 (change p 247 none)) = d6579 p
  rw [sub11790, sub11789]
  rfl
theorem sub11792 (p : Pattern) : d3567 (change p 247 none) = d6580 p := by
  change (if p 224 then d356 (change p 247 none) else d3566 (change p 247 none)) = d6580 p
  rw [sub11790, sub11791]
  rfl
theorem sub11793 (p : Pattern) : d3568 (change p 247 none) = d6581 p := by
  change (if p 204 then d3567 (change p 247 none) else d23 (change p 247 none)) = d6581 p
  rw [sub11792, sub11789]
  rfl
theorem sub11794 (p : Pattern) : d11 (change p 247 none) = d11 p := by
  rfl
theorem sub11795 (p : Pattern) : d39 (change p 247 none) = d11 p := by
  change d11 (change p 247 none) = d11 p
  exact sub11794 p
theorem sub11796 (p : Pattern) : d3569 (change p 247 none) = d6582 p := by
  change (if p 246 then d39 (change p 247 none) else d23 (change p 247 none)) = d6582 p
  rw [sub11795, sub11789]
  rfl
theorem sub11797 (p : Pattern) : d3570 (change p 247 none) = d6583 p := by
  change (if p 225 then d3569 (change p 247 none) else d23 (change p 247 none)) = d6583 p
  rw [sub11796, sub11789]
  rfl
theorem sub11798 (p : Pattern) : d3571 (change p 247 none) = d6584 p := by
  change (if p 224 then d3569 (change p 247 none) else d3570 (change p 247 none)) = d6584 p
  rw [sub11796, sub11797]
  rfl
theorem sub11799 (p : Pattern) : d3572 (change p 247 none) = d6585 p := by
  change (if p 204 then d12 (change p 247 none) else d3571 (change p 247 none)) = d6585 p
  rw [sub11767, sub11798]
  rfl
theorem sub11800 (p : Pattern) : d3573 (change p 247 none) = d6586 p := by
  change (if p 182 then d3572 (change p 247 none) else d3568 (change p 247 none)) = d6586 p
  rw [sub11799, sub11793]
  rfl
theorem sub11801 (p : Pattern) : d3574 (change p 247 none) = d6587 p := by
  change (if p 163 then d12 (change p 247 none) else d3573 (change p 247 none)) = d6587 p
  rw [sub11767, sub11800]
  rfl
theorem sub11802 (p : Pattern) : d3575 (change p 247 none) = d6588 p := by
  change (if p 162 then d3574 (change p 247 none) else d3564 (change p 247 none)) = d6588 p
  rw [sub11801, sub11786]
  rfl
theorem sub11803 (p : Pattern) : d3576 (change p 247 none) = d6589 p := by
  change (if p 161 then d3575 (change p 247 none) else d3565 (change p 247 none)) = d6589 p
  rw [sub11802, sub11787]
  rfl
theorem sub11804 (p : Pattern) : d3577 (change p 247 none) = d6590 p := by
  change (if p 246 then d34 (change p 247 none) else d13 (change p 247 none)) = d6590 p
  rw [sub11780, sub11752]
  rfl
theorem sub11805 (p : Pattern) : d3578 (change p 247 none) = d6591 p := by
  change (if p 225 then d3577 (change p 247 none) else d13 (change p 247 none)) = d6591 p
  rw [sub11804, sub11752]
  rfl
theorem sub11806 (p : Pattern) : d3579 (change p 247 none) = d6592 p := by
  change (if p 246 then d23 (change p 247 none) else d13 (change p 247 none)) = d6592 p
  rw [sub11789, sub11752]
  rfl
theorem sub11807 (p : Pattern) : d3580 (change p 247 none) = d6593 p := by
  change (if p 225 then d3579 (change p 247 none) else d3543 (change p 247 none)) = d6593 p
  rw [sub11806, sub11758]
  rfl
theorem sub11808 (p : Pattern) : d3581 (change p 247 none) = d6594 p := by
  change (if p 224 then d3580 (change p 247 none) else d3578 (change p 247 none)) = d6594 p
  rw [sub11807, sub11805]
  rfl
theorem sub11809 (p : Pattern) : d3582 (change p 247 none) = d6595 p := by
  change (if p 204 then d3581 (change p 247 none) else d13 (change p 247 none)) = d6595 p
  rw [sub11808, sub11752]
  rfl
theorem sub11810 (p : Pattern) : d3583 (change p 247 none) = d6596 p := by
  change (if p 246 then d190 (change p 247 none) else d30 (change p 247 none)) = d6596 p
  rw [sub11774, sub11763]
  rfl
theorem sub11811 (p : Pattern) : d3584 (change p 247 none) = d6597 p := by
  change (if p 225 then d3583 (change p 247 none) else d30 (change p 247 none)) = d6597 p
  rw [sub11810, sub11763]
  rfl
theorem sub11812 (p : Pattern) : d3585 (change p 247 none) = d6598 p := by
  change (if p 246 then d34 (change p 247 none) else d30 (change p 247 none)) = d6598 p
  rw [sub11780, sub11763]
  rfl
theorem sub11813 (p : Pattern) : d1715 (change p 247 none) = d6599 p := by
  change (if p 246 then d39 (change p 247 none) else d30 (change p 247 none)) = d6599 p
  rw [sub11795, sub11763]
  rfl
theorem sub11814 (p : Pattern) : d3586 (change p 247 none) = d6600 p := by
  change (if p 225 then d1715 (change p 247 none) else d3585 (change p 247 none)) = d6600 p
  rw [sub11813, sub11812]
  rfl
theorem sub11815 (p : Pattern) : d3587 (change p 247 none) = d6601 p := by
  change (if p 224 then d3586 (change p 247 none) else d3584 (change p 247 none)) = d6601 p
  rw [sub11814, sub11811]
  rfl
theorem sub11816 (p : Pattern) : d3588 (change p 247 none) = d6602 p := by
  change (if p 204 then d12 (change p 247 none) else d3587 (change p 247 none)) = d6602 p
  rw [sub11767, sub11815]
  rfl
theorem sub11817 (p : Pattern) : d3589 (change p 247 none) = d6603 p := by
  change (if p 182 then d3588 (change p 247 none) else d3582 (change p 247 none)) = d6603 p
  rw [sub11816, sub11809]
  rfl
theorem sub11818 (p : Pattern) : d364 (change p 247 none) = d3253 p := by
  change (if p 246 then d12 (change p 247 none) else d34 (change p 247 none)) = d3253 p
  rw [sub11767, sub11780]
  rfl
theorem sub11819 (p : Pattern) : d3590 (change p 247 none) = d6604 p := by
  change (if p 225 then d364 (change p 247 none) else d34 (change p 247 none)) = d6604 p
  rw [sub11818, sub11780]
  rfl
theorem sub11820 (p : Pattern) : d10 (change p 247 none) = d10 p := by
  rfl
theorem sub11821 (p : Pattern) : d57 (change p 247 none) = d10 p := by
  change d10 (change p 247 none) = d10 p
  exact sub11820 p
theorem sub11822 (p : Pattern) : d3591 (change p 247 none) = d6605 p := by
  change (if p 246 then d57 (change p 247 none) else d34 (change p 247 none)) = d6605 p
  rw [sub11821, sub11780]
  rfl
theorem sub11823 (p : Pattern) : d3592 (change p 247 none) = d6606 p := by
  change (if p 225 then d364 (change p 247 none) else d3591 (change p 247 none)) = d6606 p
  rw [sub11818, sub11822]
  rfl
theorem sub11824 (p : Pattern) : d3593 (change p 247 none) = d6607 p := by
  change (if p 224 then d3592 (change p 247 none) else d3590 (change p 247 none)) = d6607 p
  rw [sub11823, sub11819]
  rfl
theorem sub11825 (p : Pattern) : d3594 (change p 247 none) = d6608 p := by
  change (if p 204 then d12 (change p 247 none) else d3593 (change p 247 none)) = d6608 p
  rw [sub11767, sub11824]
  rfl
theorem sub11826 (p : Pattern) : d3595 (change p 247 none) = d6609 p := by
  change (if p 182 then d3594 (change p 247 none) else d3582 (change p 247 none)) = d6609 p
  rw [sub11825, sub11809]
  rfl
theorem sub11827 (p : Pattern) : d3596 (change p 247 none) = d6610 p := by
  change (if p 163 then d3595 (change p 247 none) else d3589 (change p 247 none)) = d6610 p
  rw [sub11826, sub11817]
  rfl
theorem sub11828 (p : Pattern) : d327 (change p 247 none) = d3257 p := by
  change (if p 246 then d12 (change p 247 none) else d39 (change p 247 none)) = d3257 p
  rw [sub11767, sub11795]
  rfl
theorem sub11829 (p : Pattern) : d3597 (change p 247 none) = d6611 p := by
  change (if p 225 then d327 (change p 247 none) else d39 (change p 247 none)) = d6611 p
  rw [sub11828, sub11795]
  rfl
theorem sub11830 (p : Pattern) : d3598 (change p 247 none) = d6612 p := by
  change (if p 224 then d327 (change p 247 none) else d3597 (change p 247 none)) = d6612 p
  rw [sub11828, sub11829]
  rfl
theorem sub11831 (p : Pattern) : d3599 (change p 247 none) = d6613 p := by
  change (if p 204 then d12 (change p 247 none) else d3598 (change p 247 none)) = d6613 p
  rw [sub11767, sub11830]
  rfl
theorem sub11832 (p : Pattern) : d3600 (change p 247 none) = d6614 p := by
  change (if p 182 then d3599 (change p 247 none) else d3582 (change p 247 none)) = d6614 p
  rw [sub11831, sub11809]
  rfl
theorem sub11833 (p : Pattern) : d3601 (change p 247 none) = d6615 p := by
  change (if p 246 then d57 (change p 247 none) else d17 (change p 247 none)) = d6615 p
  rw [sub11821, sub11757]
  rfl
theorem sub11834 (p : Pattern) : d3602 (change p 247 none) = d6616 p := by
  change (if p 225 then d3601 (change p 247 none) else d17 (change p 247 none)) = d6616 p
  rw [sub11833, sub11757]
  rfl
theorem sub11835 (p : Pattern) : d339 (change p 247 none) = d3239 p := by
  change (if p 246 then d12 (change p 247 none) else d17 (change p 247 none)) = d3239 p
  rw [sub11767, sub11757]
  rfl
theorem sub11836 (p : Pattern) : d3603 (change p 247 none) = d6617 p := by
  change (if p 225 then d339 (change p 247 none) else d3555 (change p 247 none)) = d6617 p
  rw [sub11835, sub11775]
  rfl
theorem sub11837 (p : Pattern) : d3604 (change p 247 none) = d6618 p := by
  change (if p 224 then d3603 (change p 247 none) else d3602 (change p 247 none)) = d6618 p
  rw [sub11836, sub11834]
  rfl
theorem sub11838 (p : Pattern) : d3605 (change p 247 none) = d6619 p := by
  change (if p 204 then d3604 (change p 247 none) else d17 (change p 247 none)) = d6619 p
  rw [sub11837, sub11757]
  rfl
theorem sub11839 (p : Pattern) : d3606 (change p 247 none) = d6620 p := by
  change (if p 182 then d12 (change p 247 none) else d3605 (change p 247 none)) = d6620 p
  rw [sub11767, sub11838]
  rfl
theorem sub11840 (p : Pattern) : d3607 (change p 247 none) = d6621 p := by
  change (if p 163 then d3606 (change p 247 none) else d3600 (change p 247 none)) = d6621 p
  rw [sub11839, sub11832]
  rfl
theorem sub11841 (p : Pattern) : d3608 (change p 247 none) = d6622 p := by
  change (if p 162 then d3607 (change p 247 none) else d3596 (change p 247 none)) = d6622 p
  rw [sub11840, sub11827]
  rfl
theorem sub11842 (p : Pattern) : d3609 (change p 247 none) = d6623 p := by
  change (if p 182 then d12 (change p 247 none) else d3582 (change p 247 none)) = d6623 p
  rw [sub11767, sub11809]
  rfl
theorem sub11843 (p : Pattern) : d3610 (change p 247 none) = d6624 p := by
  change (if p 163 then d3606 (change p 247 none) else d3609 (change p 247 none)) = d6624 p
  rw [sub11839, sub11842]
  rfl
theorem sub11844 (p : Pattern) : d3611 (change p 247 none) = d6625 p := by
  change (if p 182 then d12 (change p 247 none) else d3568 (change p 247 none)) = d6625 p
  rw [sub11767, sub11793]
  rfl
theorem sub11845 (p : Pattern) : d3612 (change p 247 none) = d6626 p := by
  change (if p 163 then d12 (change p 247 none) else d3611 (change p 247 none)) = d6626 p
  rw [sub11767, sub11844]
  rfl
theorem sub11846 (p : Pattern) : d3613 (change p 247 none) = d6627 p := by
  change (if p 162 then d3612 (change p 247 none) else d3610 (change p 247 none)) = d6627 p
  rw [sub11845, sub11843]
  rfl
theorem sub11847 (p : Pattern) : d3614 (change p 247 none) = d6628 p := by
  change (if p 161 then d3613 (change p 247 none) else d3608 (change p 247 none)) = d6628 p
  rw [sub11846, sub11841]
  rfl
theorem sub11848 (p : Pattern) : d3615 (change p 247 none) = d6629 p := by
  change (if p 160 then d3614 (change p 247 none) else d3576 (change p 247 none)) = d6629 p
  rw [sub11847, sub11803]
  rfl
theorem sub11849 (p : Pattern) : d1785 (change p 247 none) = d0 p := by
  change d0 (change p 247 none) = d0 p
  exact sub11750 p
theorem sub11850 (p : Pattern) : d3616 (change p 247 none) = d0 p := by
  change (if p 246 then d13 (change p 247 none) else d1785 (change p 247 none)) = d0 p
  rw [sub11752, sub11849]
  simp only [ite_self]
theorem sub11851 (p : Pattern) : d3617 (change p 247 none) = d0 p := by
  change (if p 225 then d13 (change p 247 none) else d3616 (change p 247 none)) = d0 p
  rw [sub11752, sub11850]
  simp only [ite_self]
theorem sub11852 (p : Pattern) : d3618 (change p 247 none) = d0 p := by
  change (if p 224 then d13 (change p 247 none) else d3617 (change p 247 none)) = d0 p
  rw [sub11752, sub11851]
  simp only [ite_self]
theorem sub11853 (p : Pattern) : d3619 (change p 247 none) = d6562 p := by
  change (if p 204 then d3545 (change p 247 none) else d3618 (change p 247 none)) = d6562 p
  rw [sub11760, sub11852]
  rfl
theorem sub11854 (p : Pattern) : d3620 (change p 247 none) = d6567 p := by
  change (if p 182 then d3550 (change p 247 none) else d3619 (change p 247 none)) = d6567 p
  rw [sub11768, sub11853]
  rfl
theorem sub11855 (p : Pattern) : d3621 (change p 247 none) = d6630 p := by
  change (if p 225 then d3585 (change p 247 none) else d30 (change p 247 none)) = d6630 p
  rw [sub11812, sub11763]
  rfl
theorem sub11856 (p : Pattern) : d3622 (change p 247 none) = d6631 p := by
  change (if p 224 then d3585 (change p 247 none) else d3621 (change p 247 none)) = d6631 p
  rw [sub11812, sub11855]
  rfl
theorem sub11857 (p : Pattern) : d3623 (change p 247 none) = d6632 p := by
  change (if p 204 then d3622 (change p 247 none) else d30 (change p 247 none)) = d6632 p
  rw [sub11856, sub11763]
  rfl
theorem sub11858 (p : Pattern) : d3624 (change p 247 none) = d6633 p := by
  change (if p 246 then d17 (change p 247 none) else d30 (change p 247 none)) = d6633 p
  rw [sub11757, sub11763]
  rfl
theorem sub11859 (p : Pattern) : d3625 (change p 247 none) = d6634 p := by
  change (if p 225 then d3624 (change p 247 none) else d30 (change p 247 none)) = d6634 p
  rw [sub11858, sub11763]
  rfl
theorem sub11860 (p : Pattern) : d3626 (change p 247 none) = d6635 p := by
  change (if p 224 then d3624 (change p 247 none) else d3625 (change p 247 none)) = d6635 p
  rw [sub11858, sub11859]
  rfl
theorem sub11861 (p : Pattern) : d3627 (change p 247 none) = d6636 p := by
  change (if p 204 then d12 (change p 247 none) else d3626 (change p 247 none)) = d6636 p
  rw [sub11767, sub11860]
  rfl
theorem sub11862 (p : Pattern) : d3628 (change p 247 none) = d6637 p := by
  change (if p 182 then d3627 (change p 247 none) else d3623 (change p 247 none)) = d6637 p
  rw [sub11861, sub11857]
  rfl
theorem sub11863 (p : Pattern) : d3629 (change p 247 none) = d6638 p := by
  change (if p 163 then d3628 (change p 247 none) else d3620 (change p 247 none)) = d6638 p
  rw [sub11862, sub11854]
  rfl
theorem sub11864 (p : Pattern) : d3630 (change p 247 none) = d6639 p := by
  change (if p 163 then d3573 (change p 247 none) else d3563 (change p 247 none)) = d6639 p
  rw [sub11800, sub11785]
  rfl
theorem sub11865 (p : Pattern) : d3631 (change p 247 none) = d6640 p := by
  change (if p 162 then d3630 (change p 247 none) else d3629 (change p 247 none)) = d6640 p
  rw [sub11864, sub11863]
  rfl
theorem sub11866 (p : Pattern) : d329 (change p 247 none) = d3279 p := by
  change (if p 246 then d12 (change p 247 none) else d57 (change p 247 none)) = d3279 p
  rw [sub11767, sub11821]
  rfl
theorem sub11867 (p : Pattern) : d3632 (change p 247 none) = d6641 p := by
  change (if p 225 then d329 (change p 247 none) else d57 (change p 247 none)) = d6641 p
  rw [sub11866, sub11821]
  rfl
theorem sub11868 (p : Pattern) : d3633 (change p 247 none) = d6642 p := by
  change (if p 224 then d329 (change p 247 none) else d3632 (change p 247 none)) = d6642 p
  rw [sub11866, sub11867]
  rfl
theorem sub11869 (p : Pattern) : d3634 (change p 247 none) = d6643 p := by
  change (if p 204 then d3633 (change p 247 none) else d57 (change p 247 none)) = d6643 p
  rw [sub11868, sub11821]
  rfl
theorem sub11870 (p : Pattern) : d3635 (change p 247 none) = d6644 p := by
  change (if p 204 then d12 (change p 247 none) else d3633 (change p 247 none)) = d6644 p
  rw [sub11767, sub11868]
  rfl
theorem sub11871 (p : Pattern) : d3636 (change p 247 none) = d6645 p := by
  change (if p 182 then d3635 (change p 247 none) else d3634 (change p 247 none)) = d6645 p
  rw [sub11870, sub11869]
  rfl
theorem sub11872 (p : Pattern) : d3637 (change p 247 none) = d6646 p := by
  change (if p 163 then d3636 (change p 247 none) else d3563 (change p 247 none)) = d6646 p
  rw [sub11871, sub11785]
  rfl
theorem sub11873 (p : Pattern) : d3638 (change p 247 none) = d6647 p := by
  change (if p 204 then d3598 (change p 247 none) else d39 (change p 247 none)) = d6647 p
  rw [sub11830, sub11795]
  rfl
theorem sub11874 (p : Pattern) : d3639 (change p 247 none) = d6648 p := by
  change (if p 182 then d3599 (change p 247 none) else d3638 (change p 247 none)) = d6648 p
  rw [sub11831, sub11873]
  rfl
theorem sub11875 (p : Pattern) : d3640 (change p 247 none) = d6649 p := by
  change (if p 163 then d12 (change p 247 none) else d3639 (change p 247 none)) = d6649 p
  rw [sub11767, sub11874]
  rfl
theorem sub11876 (p : Pattern) : d3641 (change p 247 none) = d6650 p := by
  change (if p 162 then d3640 (change p 247 none) else d3637 (change p 247 none)) = d6650 p
  rw [sub11875, sub11872]
  rfl
theorem sub11877 (p : Pattern) : d3642 (change p 247 none) = d6651 p := by
  change (if p 161 then d3641 (change p 247 none) else d3631 (change p 247 none)) = d6651 p
  rw [sub11876, sub11865]
  rfl
theorem sub11878 (p : Pattern) : d3643 (change p 247 none) = d6652 p := by
  change (if p 204 then d3587 (change p 247 none) else d30 (change p 247 none)) = d6652 p
  rw [sub11815, sub11763]
  rfl
theorem sub11879 (p : Pattern) : d3644 (change p 247 none) = d6653 p := by
  change (if p 182 then d12 (change p 247 none) else d3643 (change p 247 none)) = d6653 p
  rw [sub11767, sub11878]
  rfl
end NetHack.Sokoban22Refined85
