/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons026
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c3780 (pattern : Twelve) (guard : d1866 pattern = 1) : d91 pattern ≤ (0 : Int) + d743 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d91, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3776 pattern childGuard
    simpa only [d91, d743, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d91, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3779 pattern childGuard
    simpa only [d91, d743, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3781 (pattern : Twelve) (guard : d1866 pattern = 1) : d31 pattern ≤ (0 : Int) + d673 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d31, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d31, d673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d31, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3697 pattern childGuard
    simpa only [d31, d673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3782 (pattern : Twelve) (guard : d1866 pattern = 1) : d52 pattern ≤ (0 : Int) + d701 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3730 pattern childGuard
    simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3781 pattern childGuard
    simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3783 (pattern : Twelve) (guard : d1866 pattern = 1) : d53 pattern ≤ (0 : Int) + d702 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3730 pattern childGuard
    simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3703 pattern childGuard
    simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3784 (pattern : Twelve) (guard : d1866 pattern = 1) : d74 pattern ≤ (0 : Int) + d724 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d74, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3782 pattern childGuard
    simpa only [d74, d724, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d74, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3783 pattern childGuard
    simpa only [d74, d724, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3785 (pattern : Twelve) (guard : d1866 pattern = 1) : d54 pattern ≤ (0 : Int) + d703 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d54, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3730 pattern childGuard
    simpa only [d54, d703, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d54, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3707 pattern childGuard
    simpa only [d54, d703, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3786 (pattern : Twelve) (guard : d1866 pattern = 1) : d75 pattern ≤ (0 : Int) + d725 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d75, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3785 pattern childGuard
    simpa only [d75, d725, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d75, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3711 pattern childGuard
    simpa only [d75, d725, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3787 (pattern : Twelve) (guard : d1866 pattern = 1) : d92 pattern ≤ (0 : Int) + d744 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d92, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3784 pattern childGuard
    simpa only [d92, d744, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d92, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3786 pattern childGuard
    simpa only [d92, d744, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3788 (pattern : Twelve) (guard : d1866 pattern = 1) : d102 pattern ≤ (0 : Int) + d758 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d102, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3780 pattern childGuard
    simpa only [d102, d758, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d102, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3787 pattern childGuard
    simpa only [d102, d758, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3789 (pattern : Twelve) (guard : d1866 pattern = 1) : d76 pattern ≤ (0 : Int) + d726 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d76, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d76, d726, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d76, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3711 pattern childGuard
    simpa only [d76, d726, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3790 (pattern : Twelve) (guard : d1866 pattern = 1) : d93 pattern ≤ (0 : Int) + d745 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d93, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3776 pattern childGuard
    simpa only [d93, d745, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d93, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3789 pattern childGuard
    simpa only [d93, d745, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3791 (pattern : Twelve) (guard : d1866 pattern = 1) : d77 pattern ≤ (0 : Int) + d692 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3734 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3732 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3792 (pattern : Twelve) (guard : d1866 pattern = 1) : d94 pattern ≤ (0 : Int) + d746 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d94, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3791 pattern childGuard
    simpa only [d94, d746, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d94, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3735 pattern childGuard
    simpa only [d94, d746, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3793 (pattern : Twelve) (guard : d1866 pattern = 1) : d103 pattern ≤ (0 : Int) + d759 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d103, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3790 pattern childGuard
    simpa only [d103, d759, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d103, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3792 pattern childGuard
    simpa only [d103, d759, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3794 (pattern : Twelve) (guard : d1866 pattern = 1) : d110 pattern ≤ (0 : Int) + d768 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d110, d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3788 pattern childGuard
    simpa only [d110, d768, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d110, d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3793 pattern childGuard
    simpa only [d110, d768, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3795 (pattern : Twelve) (guard : d1866 pattern = 1) : d58 pattern ≤ (0 : Int) + d704 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d58, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3730 pattern childGuard
    simpa only [d58, d704, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d58, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3743 pattern childGuard
    simpa only [d58, d704, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3796 (pattern : Twelve) (guard : d1866 pattern = 1) : d79 pattern ≤ (0 : Int) + d727 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d79, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3730 pattern childGuard
    simpa only [d79, d727, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d79, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3795 pattern childGuard
    simpa only [d79, d727, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3797 (pattern : Twelve) (guard : d1866 pattern = 1) : d80 pattern ≤ (0 : Int) + d728 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d80, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3730 pattern childGuard
    simpa only [d80, d728, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d80, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3711 pattern childGuard
    simpa only [d80, d728, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3798 (pattern : Twelve) (guard : d1866 pattern = 1) : d95 pattern ≤ (0 : Int) + d747 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d95, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3796 pattern childGuard
    simpa only [d95, d747, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d95, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3797 pattern childGuard
    simpa only [d95, d747, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3799 (pattern : Twelve) (guard : d1866 pattern = 1) : d81 pattern ≤ (0 : Int) + d697 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3757 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3755 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3800 (pattern : Twelve) (guard : d1866 pattern = 1) : d96 pattern ≤ (0 : Int) + d748 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d96, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3799 pattern childGuard
    simpa only [d96, d748, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d96, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3763 pattern childGuard
    simpa only [d96, d748, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3801 (pattern : Twelve) (guard : d1866 pattern = 1) : d104 pattern ≤ (0 : Int) + d760 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d104, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3798 pattern childGuard
    simpa only [d104, d760, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d104, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3800 pattern childGuard
    simpa only [d104, d760, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3802 (pattern : Twelve) (guard : d1866 pattern = 1) : d105 pattern ≤ (0 : Int) + d761 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d105, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3792 pattern childGuard
    simpa only [d105, d761, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d105, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d105, d761, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3803 (pattern : Twelve) (guard : d1866 pattern = 1) : d111 pattern ≤ (0 : Int) + d769 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d111, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3801 pattern childGuard
    simpa only [d111, d769, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d111, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3802 pattern childGuard
    simpa only [d111, d769, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3804 (pattern : Twelve) (guard : d1866 pattern = 1) : d114 pattern ≤ (0 : Int) + d773 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d114, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3794 pattern childGuard
    simpa only [d114, d773, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d114, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3803 pattern childGuard
    simpa only [d114, d773, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3805 (pattern : Twelve) (guard : d1866 pattern = 1) : d114 pattern ≤ (0 : Int) + d775 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3773 pattern childGuard
    simpa only [d775, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3804 pattern childGuard
    simpa only [d775, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3806 (pattern : Twelve) (guard : d1866 pattern = 1) : d114 pattern ≤ (0 : Int) + d776 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3805 pattern childGuard
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3804 pattern childGuard
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3807 (pattern : Twelve) (guard : d1866 pattern = 1) : d120 pattern ≤ (0 : Int) + d674 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d120, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d120, d674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d120, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3760 pattern childGuard
    simpa only [d120, d674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3808 (pattern : Twelve) (guard : d1866 pattern = 1) : d129 pattern ≤ (0 : Int) + d705 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d129, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3807 pattern childGuard
    simpa only [d129, d705, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d129, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3689 pattern childGuard
    simpa only [d129, d705, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3809 (pattern : Twelve) (guard : d1866 pattern = 1) : d136 pattern ≤ (0 : Int) + d729 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d136, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d136, d729, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d136, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3808 pattern childGuard
    simpa only [d136, d729, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3810 (pattern : Twelve) (guard : d1866 pattern = 1) : d144 pattern ≤ (0 : Int) + d749 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d144, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3776 pattern childGuard
    simpa only [d144, d749, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d144, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3809 pattern childGuard
    simpa only [d144, d749, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3811 (pattern : Twelve) (guard : d1866 pattern = 1) : d121 pattern ≤ (0 : Int) + d657 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d121, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d121, d657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d121, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3709 pattern childGuard
    simpa only [d121, d657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3812 (pattern : Twelve) (guard : d1866 pattern = 1) : d130 pattern ≤ (0 : Int) + d692 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d130, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3811 pattern childGuard
    simpa only [d130, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d130, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3731 pattern childGuard
    simpa only [d130, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3813 (pattern : Twelve) (guard : d1866 pattern = 1) : d137 pattern ≤ (0 : Int) + d730 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d137, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3782 pattern childGuard
    simpa only [d137, d730, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d137, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3812 pattern childGuard
    simpa only [d137, d730, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3814 (pattern : Twelve) (guard : d1866 pattern = 1) : d138 pattern ≤ (0 : Int) + d731 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d138, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3734 pattern childGuard
    simpa only [d138, d731, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d138, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3808 pattern childGuard
    simpa only [d138, d731, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3815 (pattern : Twelve) (guard : d1866 pattern = 1) : d145 pattern ≤ (0 : Int) + d750 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d145, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3813 pattern childGuard
    simpa only [d145, d750, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d145, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3814 pattern childGuard
    simpa only [d145, d750, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3816 (pattern : Twelve) (guard : d1866 pattern = 1) : d149 pattern ≤ (0 : Int) + d762 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d149, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3810 pattern childGuard
    simpa only [d149, d762, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d149, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3815 pattern childGuard
    simpa only [d149, d762, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3817 (pattern : Twelve) (guard : d1866 pattern = 1) : d139 pattern ≤ (0 : Int) + d692 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3734 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3812 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3818 (pattern : Twelve) (guard : d1866 pattern = 1) : d146 pattern ≤ (0 : Int) + d751 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d146, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3817 pattern childGuard
    simpa only [d146, d751, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d146, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3814 pattern childGuard
    simpa only [d146, d751, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3819 (pattern : Twelve) (guard : d1866 pattern = 1) : d150 pattern ≤ (0 : Int) + d763 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d150, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3810 pattern childGuard
    simpa only [d150, d763, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d150, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3818 pattern childGuard
    simpa only [d150, d763, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3820 (pattern : Twelve) (guard : d1866 pattern = 1) : d153 pattern ≤ (0 : Int) + d770 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d153, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3816 pattern childGuard
    simpa only [d153, d770, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d153, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3819 pattern childGuard
    simpa only [d153, d770, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3821 (pattern : Twelve) (guard : d1866 pattern = 1) : d122 pattern ≤ (0 : Int) + d675 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d122, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d122, d675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d122, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3358 pattern childGuard
    simpa only [d122, d675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3822 (pattern : Twelve) (guard : d1866 pattern = 1) : d131 pattern ≤ (0 : Int) + d706 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d131, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3811 pattern childGuard
    simpa only [d131, d706, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d131, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3821 pattern childGuard
    simpa only [d131, d706, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3823 (pattern : Twelve) (guard : d1866 pattern = 1) : d140 pattern ≤ (0 : Int) + d732 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d140, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3730 pattern childGuard
    simpa only [d140, d732, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d140, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3822 pattern childGuard
    simpa only [d140, d732, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3824 (pattern : Twelve) (guard : d1866 pattern = 1) : d123 pattern ≤ (0 : Int) + d666 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d123, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d123, d666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d123, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3346 pattern childGuard
    simpa only [d123, d666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3825 (pattern : Twelve) (guard : d1866 pattern = 1) : d132 pattern ≤ (0 : Int) + d704 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d132, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3730 pattern childGuard
    simpa only [d132, d704, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d132, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3824 pattern childGuard
    simpa only [d132, d704, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3826 (pattern : Twelve) (guard : d1866 pattern = 1) : d141 pattern ≤ (0 : Int) + d733 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d141, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3825 pattern childGuard
    simpa only [d141, d733, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d141, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3808 pattern childGuard
    simpa only [d141, d733, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3827 (pattern : Twelve) (guard : d1866 pattern = 1) : d147 pattern ≤ (0 : Int) + d752 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d147, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3823 pattern childGuard
    simpa only [d147, d752, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d147, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3826 pattern childGuard
    simpa only [d147, d752, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3828 (pattern : Twelve) (guard : d1866 pattern = 1) : d14 pattern ≤ (0 : Int) + d14 pattern := by
  omega
theorem c3829 (pattern : Twelve) (guard : d1866 pattern = 1) : d118 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3444 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3828 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3830 (pattern : Twelve) (guard : d1866 pattern = 1) : d124 pattern ≤ (0 : Int) + d676 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d124, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d124, d676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d124, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3829 pattern childGuard
    simpa only [d124, d676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3831 (pattern : Twelve) (guard : d1866 pattern = 1) : d119 pattern ≤ (0 : Int) + d159 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3346 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3548 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3832 (pattern : Twelve) (guard : d1866 pattern = 1) : d125 pattern ≤ (0 : Int) + d677 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d125, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3831 pattern childGuard
    simpa only [d125, d677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d125, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d125, d677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3833 (pattern : Twelve) (guard : d1866 pattern = 1) : d133 pattern ≤ (0 : Int) + d707 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d133, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3830 pattern childGuard
    simpa only [d133, d707, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d133, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3832 pattern childGuard
    simpa only [d133, d707, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3834 (pattern : Twelve) (guard : d1866 pattern = 1) : d142 pattern ≤ (0 : Int) + d734 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d142, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3757 pattern childGuard
    simpa only [d142, d734, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d142, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3833 pattern childGuard
    simpa only [d142, d734, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3835 (pattern : Twelve) (guard : d1866 pattern = 1) : d126 pattern ≤ (0 : Int) + d676 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d126, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d126, d676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d126, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3444 pattern childGuard
    simpa only [d126, d676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3836 (pattern : Twelve) (guard : d1866 pattern = 1) : d47 pattern ≤ (0 : Int) + d677 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d47, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3346 pattern childGuard
    simpa only [d47, d677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d47, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d47, d677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3837 (pattern : Twelve) (guard : d1866 pattern = 1) : d134 pattern ≤ (0 : Int) + d707 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d134, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3835 pattern childGuard
    simpa only [d134, d707, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d134, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3836 pattern childGuard
    simpa only [d134, d707, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3838 (pattern : Twelve) (guard : d1866 pattern = 1) : d127 pattern ≤ (0 : Int) + d678 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d127, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3709 pattern childGuard
    simpa only [d127, d678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d127, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3706 pattern childGuard
    simpa only [d127, d678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3839 (pattern : Twelve) (guard : d1866 pattern = 1) : d128 pattern ≤ (0 : Int) + d679 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d128, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3697 pattern childGuard
    simpa only [d128, d679, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d128, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d128, d679, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3840 (pattern : Twelve) (guard : d1866 pattern = 1) : d135 pattern ≤ (0 : Int) + d708 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d135, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3838 pattern childGuard
    simpa only [d135, d708, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d135, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3839 pattern childGuard
    simpa only [d135, d708, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3841 (pattern : Twelve) (guard : d1866 pattern = 1) : d143 pattern ≤ (0 : Int) + d735 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d143, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3837 pattern childGuard
    simpa only [d143, d735, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d143, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3840 pattern childGuard
    simpa only [d143, d735, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3842 (pattern : Twelve) (guard : d1866 pattern = 1) : d148 pattern ≤ (0 : Int) + d753 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d148, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3834 pattern childGuard
    simpa only [d148, d753, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d148, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3841 pattern childGuard
    simpa only [d148, d753, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3843 (pattern : Twelve) (guard : d1866 pattern = 1) : d151 pattern ≤ (0 : Int) + d764 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d151, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3827 pattern childGuard
    simpa only [d151, d764, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d151, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3842 pattern childGuard
    simpa only [d151, d764, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3844 (pattern : Twelve) (guard : d1866 pattern = 1) : d152 pattern ≤ (0 : Int) + d765 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d152, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3818 pattern childGuard
    simpa only [d152, d765, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d152, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d152, d765, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3845 (pattern : Twelve) (guard : d1866 pattern = 1) : d154 pattern ≤ (0 : Int) + d771 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d154, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3843 pattern childGuard
    simpa only [d154, d771, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d154, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3844 pattern childGuard
    simpa only [d154, d771, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3846 (pattern : Twelve) (guard : d1866 pattern = 1) : d155 pattern ≤ (0 : Int) + d774 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d155, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3820 pattern childGuard
    simpa only [d155, d774, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d155, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3845 pattern childGuard
    simpa only [d155, d774, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3847 (pattern : Twelve) (guard : d1866 pattern = 1) : d156 pattern ≤ (0 : Int) + d777 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d156, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3806 pattern childGuard
    simpa only [d156, d777, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d156, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3846 pattern childGuard
    simpa only [d156, d777, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3848 (pattern : Twelve) (guard : d1866 pattern = 1) : d814 pattern ≤ (0 : Int) + d636 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d814, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3468 pattern childGuard
    simpa only [d814, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d814, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3258 pattern childGuard
    simpa only [d814, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3849 (pattern : Twelve) (guard : d1866 pattern = 1) : d816 pattern ≤ (0 : Int) + d1183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d816, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3848 pattern childGuard
    simpa only [d816, d1183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d816, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3258 pattern childGuard
    simpa only [d816, d1183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3850 (pattern : Twelve) (guard : d1866 pattern = 1) : d824 pattern ≤ (0 : Int) + d1189 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d824, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3679 pattern childGuard
    simpa only [d824, d1189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d824, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3849 pattern childGuard
    simpa only [d824, d1189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3851 (pattern : Twelve) (guard : d1866 pattern = 1) : d838 pattern ≤ (0 : Int) + d1199 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d838, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3684 pattern childGuard
    simpa only [d838, d1199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d838, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3850 pattern childGuard
    simpa only [d838, d1199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3852 (pattern : Twelve) (guard : d1866 pattern = 1) : d17 pattern ≤ (0 : Int) + d649 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3678 pattern childGuard
    simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3853 (pattern : Twelve) (guard : d1866 pattern = 1) : d17 pattern ≤ (0 : Int) + d1190 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3852 pattern childGuard
    simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3854 (pattern : Twelve) (guard : d1866 pattern = 1) : d817 pattern ≤ (0 : Int) + d1184 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d817, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3687 pattern childGuard
    simpa only [d817, d1184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d817, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3760 pattern childGuard
    simpa only [d817, d1184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3855 (pattern : Twelve) (guard : d1866 pattern = 1) : d825 pattern ≤ (0 : Int) + d1191 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d825, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3854 pattern childGuard
    simpa only [d825, d1191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d825, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3761 pattern childGuard
    simpa only [d825, d1191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3856 (pattern : Twelve) (guard : d1866 pattern = 1) : d839 pattern ≤ (0 : Int) + d1200 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d839, d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3853 pattern childGuard
    simpa only [d839, d1200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d839, d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3855 pattern childGuard
    simpa only [d839, d1200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3857 (pattern : Twelve) (guard : d1866 pattern = 1) : d853 pattern ≤ (0 : Int) + d1216 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d853, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3851 pattern childGuard
    simpa only [d853, d1216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d853, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3856 pattern childGuard
    simpa only [d853, d1216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3858 (pattern : Twelve) (guard : d1866 pattern = 1) : d56 pattern ≤ (0 : Int) + d1192 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d56, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3700 pattern childGuard
    simpa only [d56, d1192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d56, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3728 pattern childGuard
    simpa only [d56, d1192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3859 (pattern : Twelve) (guard : d1866 pattern = 1) : d818 pattern ≤ (0 : Int) + d651 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d818, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3848 pattern childGuard
    simpa only [d818, d651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d818, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d818, d651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3860 (pattern : Twelve) (guard : d1866 pattern = 1) : d826 pattern ≤ (0 : Int) + d687 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d826, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3710 pattern childGuard
    simpa only [d826, d687, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d826, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3859 pattern childGuard
    simpa only [d826, d687, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3861 (pattern : Twelve) (guard : d1866 pattern = 1) : d840 pattern ≤ (0 : Int) + d1201 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d840, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3858 pattern childGuard
    simpa only [d840, d1201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d840, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3860 pattern childGuard
    simpa only [d840, d1201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3862 (pattern : Twelve) (guard : d1866 pattern = 1) : d827 pattern ≤ (0 : Int) + d692 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d827, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3710 pattern childGuard
    simpa only [d827, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d827, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3731 pattern childGuard
    simpa only [d827, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3863 (pattern : Twelve) (guard : d1866 pattern = 1) : d841 pattern ≤ (0 : Int) + d1202 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d841, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3862 pattern childGuard
    simpa only [d841, d1202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d841, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3855 pattern childGuard
    simpa only [d841, d1202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3864 (pattern : Twelve) (guard : d1866 pattern = 1) : d854 pattern ≤ (0 : Int) + d1217 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d854, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3861 pattern childGuard
    simpa only [d854, d1217, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d854, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3863 pattern childGuard
    simpa only [d854, d1217, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3865 (pattern : Twelve) (guard : d1866 pattern = 1) : d861 pattern ≤ (0 : Int) + d1228 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d861, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3857 pattern childGuard
    simpa only [d861, d1228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d861, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3864 pattern childGuard
    simpa only [d861, d1228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3866 (pattern : Twelve) (guard : d1866 pattern = 1) : d824 pattern ≤ (0 : Int) + d1193 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d824, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3720 pattern childGuard
    simpa only [d824, d1193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d824, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3849 pattern childGuard
    simpa only [d824, d1193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3867 (pattern : Twelve) (guard : d1866 pattern = 1) : d838 pattern ≤ (0 : Int) + d1203 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d838, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3723 pattern childGuard
    simpa only [d838, d1203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d838, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3866 pattern childGuard
    simpa only [d838, d1203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3868 (pattern : Twelve) (guard : d1866 pattern = 1) : d839 pattern ≤ (0 : Int) + d1204 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d839, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d839, d1204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d839, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3855 pattern childGuard
    simpa only [d839, d1204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3869 (pattern : Twelve) (guard : d1866 pattern = 1) : d853 pattern ≤ (0 : Int) + d1218 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d853, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3867 pattern childGuard
    simpa only [d853, d1218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d853, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3868 pattern childGuard
    simpa only [d853, d1218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3870 (pattern : Twelve) (guard : d1866 pattern = 1) : d840 pattern ≤ (0 : Int) + d716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d840, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3734 pattern childGuard
    simpa only [d840, d716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d840, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3860 pattern childGuard
    simpa only [d840, d716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3871 (pattern : Twelve) (guard : d1866 pattern = 1) : d854 pattern ≤ (0 : Int) + d1219 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d854, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3870 pattern childGuard
    simpa only [d854, d1219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d854, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3863 pattern childGuard
    simpa only [d854, d1219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3872 (pattern : Twelve) (guard : d1866 pattern = 1) : d861 pattern ≤ (0 : Int) + d1229 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d861, d1229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3869 pattern childGuard
    simpa only [d861, d1229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d861, d1229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3871 pattern childGuard
    simpa only [d861, d1229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3873 (pattern : Twelve) (guard : d1866 pattern = 1) : d861 pattern ≤ (0 : Int) + d1237 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3865 pattern childGuard
    simpa only [d1237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3872 pattern childGuard
    simpa only [d1237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3874 (pattern : Twelve) (guard : d1866 pattern = 1) : d819 pattern ≤ (0 : Int) + d1185 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d819, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3848 pattern childGuard
    simpa only [d819, d1185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d819, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3346 pattern childGuard
    simpa only [d819, d1185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3875 (pattern : Twelve) (guard : d1866 pattern = 1) : d828 pattern ≤ (0 : Int) + d1194 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d828, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3710 pattern childGuard
    simpa only [d828, d1194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d828, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3874 pattern childGuard
    simpa only [d828, d1194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3876 (pattern : Twelve) (guard : d1866 pattern = 1) : d842 pattern ≤ (0 : Int) + d1205 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d842, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3746 pattern childGuard
    simpa only [d842, d1205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d842, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3875 pattern childGuard
    simpa only [d842, d1205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3877 (pattern : Twelve) (guard : d1866 pattern = 1) : d843 pattern ≤ (0 : Int) + d1206 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d843, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3710 pattern childGuard
    simpa only [d843, d1206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d843, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3855 pattern childGuard
    simpa only [d843, d1206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3878 (pattern : Twelve) (guard : d1866 pattern = 1) : d855 pattern ≤ (0 : Int) + d1220 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d855, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3876 pattern childGuard
    simpa only [d855, d1220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d855, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3877 pattern childGuard
    simpa only [d855, d1220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3879 (pattern : Twelve) (guard : d1866 pattern = 1) : d815 pattern ≤ (0 : Int) + d644 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d815, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3500 pattern childGuard
    simpa only [d815, d644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d815, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3346 pattern childGuard
    simpa only [d815, d644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3880 (pattern : Twelve) (guard : d1866 pattern = 1) : d820 pattern ≤ (0 : Int) + d670 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d820, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3879 pattern childGuard
    simpa only [d820, d670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d820, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d820, d670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3881 (pattern : Twelve) (guard : d1866 pattern = 1) : d829 pattern ≤ (0 : Int) + d698 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d829, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3759 pattern childGuard
    simpa only [d829, d698, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d829, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3880 pattern childGuard
    simpa only [d829, d698, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3882 (pattern : Twelve) (guard : d1866 pattern = 1) : d844 pattern ≤ (0 : Int) + d720 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d844, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3757 pattern childGuard
    simpa only [d844, d720, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d844, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3881 pattern childGuard
    simpa only [d844, d720, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3883 (pattern : Twelve) (guard : d1866 pattern = 1) : d830 pattern ≤ (0 : Int) + d697 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d830, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3759 pattern childGuard
    simpa only [d830, d697, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d830, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3754 pattern childGuard
    simpa only [d830, d697, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3884 (pattern : Twelve) (guard : d1866 pattern = 1) : d821 pattern ≤ (0 : Int) + d1186 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d821, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3760 pattern childGuard
    simpa only [d821, d1186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d821, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3702 pattern childGuard
    simpa only [d821, d1186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3885 (pattern : Twelve) (guard : d1866 pattern = 1) : d822 pattern ≤ (0 : Int) + d822 pattern := by
  omega
theorem c3886 (pattern : Twelve) (guard : d1866 pattern = 1) : d831 pattern ≤ (0 : Int) + d1195 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d831, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3884 pattern childGuard
    simpa only [d831, d1195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d831, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3885 pattern childGuard
    simpa only [d831, d1195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3887 (pattern : Twelve) (guard : d1866 pattern = 1) : d845 pattern ≤ (0 : Int) + d1207 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d845, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3883 pattern childGuard
    simpa only [d845, d1207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d845, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3886 pattern childGuard
    simpa only [d845, d1207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3888 (pattern : Twelve) (guard : d1866 pattern = 1) : d856 pattern ≤ (0 : Int) + d1221 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d856, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3882 pattern childGuard
    simpa only [d856, d1221, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d856, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3887 pattern childGuard
    simpa only [d856, d1221, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3889 (pattern : Twelve) (guard : d1866 pattern = 1) : d862 pattern ≤ (0 : Int) + d1230 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d862, d1230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3878 pattern childGuard
    simpa only [d862, d1230, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d862, d1230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3888 pattern childGuard
    simpa only [d862, d1230, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3890 (pattern : Twelve) (guard : d1866 pattern = 1) : d863 pattern ≤ (0 : Int) + d1231 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d863, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3871 pattern childGuard
    simpa only [d863, d1231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d863, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d863, d1231, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3891 (pattern : Twelve) (guard : d1866 pattern = 1) : d867 pattern ≤ (0 : Int) + d1238 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d867, d1238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3889 pattern childGuard
    simpa only [d867, d1238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d867, d1238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3890 pattern childGuard
    simpa only [d867, d1238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3892 (pattern : Twelve) (guard : d1866 pattern = 1) : d869 pattern ≤ (0 : Int) + d1241 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d869, d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3873 pattern childGuard
    simpa only [d869, d1241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d869, d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3891 pattern childGuard
    simpa only [d869, d1241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3893 (pattern : Twelve) (guard : d1866 pattern = 1) : d838 pattern ≤ (0 : Int) + d1208 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d838, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d838, d1208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d838, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3866 pattern childGuard
    simpa only [d838, d1208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3894 (pattern : Twelve) (guard : d1866 pattern = 1) : d853 pattern ≤ (0 : Int) + d1222 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d853, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3893 pattern childGuard
    simpa only [d853, d1222, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d853, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3868 pattern childGuard
    simpa only [d853, d1222, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3895 (pattern : Twelve) (guard : d1866 pattern = 1) : d861 pattern ≤ (0 : Int) + d1232 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d861, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3894 pattern childGuard
    simpa only [d861, d1232, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d861, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3871 pattern childGuard
    simpa only [d861, d1232, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3896 (pattern : Twelve) (guard : d1866 pattern = 1) : d842 pattern ≤ (0 : Int) + d1209 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d842, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3730 pattern childGuard
    simpa only [d842, d1209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d842, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3875 pattern childGuard
    simpa only [d842, d1209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3897 (pattern : Twelve) (guard : d1866 pattern = 1) : d855 pattern ≤ (0 : Int) + d1223 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d855, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3896 pattern childGuard
    simpa only [d855, d1223, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d855, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3877 pattern childGuard
    simpa only [d855, d1223, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3898 (pattern : Twelve) (guard : d1866 pattern = 1) : d862 pattern ≤ (0 : Int) + d1233 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d862, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3897 pattern childGuard
    simpa only [d862, d1233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d862, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3888 pattern childGuard
    simpa only [d862, d1233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3899 (pattern : Twelve) (guard : d1866 pattern = 1) : d867 pattern ≤ (0 : Int) + d1239 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d867, d1239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3898 pattern childGuard
    simpa only [d867, d1239, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d867, d1239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3890 pattern childGuard
    simpa only [d867, d1239, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3900 (pattern : Twelve) (guard : d1866 pattern = 1) : d869 pattern ≤ (0 : Int) + d1242 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d869, d1242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3895 pattern childGuard
    simpa only [d869, d1242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d869, d1242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3899 pattern childGuard
    simpa only [d869, d1242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3901 (pattern : Twelve) (guard : d1866 pattern = 1) : d869 pattern ≤ (0 : Int) + d1244 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3892 pattern childGuard
    simpa only [d1244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3900 pattern childGuard
    simpa only [d1244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3902 (pattern : Twelve) (guard : d1866 pattern = 1) : d869 pattern ≤ (0 : Int) + d1245 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3901 pattern childGuard
    simpa only [d1245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3900 pattern childGuard
    simpa only [d1245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3903 (pattern : Twelve) (guard : d1866 pattern = 1) : d872 pattern ≤ (0 : Int) + d157 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3258 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3268 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3904 (pattern : Twelve) (guard : d1866 pattern = 1) : d874 pattern ≤ (0 : Int) + d661 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d874, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d874, d661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d874, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3903 pattern childGuard
    simpa only [d874, d661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3905 (pattern : Twelve) (guard : d1866 pattern = 1) : d875 pattern ≤ (0 : Int) + d1183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d875, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3848 pattern childGuard
    simpa only [d875, d1183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d875, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3903 pattern childGuard
    simpa only [d875, d1183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3906 (pattern : Twelve) (guard : d1866 pattern = 1) : d882 pattern ≤ (0 : Int) + d1193 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d882, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3904 pattern childGuard
    simpa only [d882, d1193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d882, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3905 pattern childGuard
    simpa only [d882, d1193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3907 (pattern : Twelve) (guard : d1866 pattern = 1) : d890 pattern ≤ (0 : Int) + d1208 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d890, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d890, d1208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d890, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3906 pattern childGuard
    simpa only [d890, d1208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3908 (pattern : Twelve) (guard : d1866 pattern = 1) : d876 pattern ≤ (0 : Int) + d1187 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d876, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3687 pattern childGuard
    simpa only [d876, d1187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d876, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3702 pattern childGuard
    simpa only [d876, d1187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3909 (pattern : Twelve) (guard : d1866 pattern = 1) : d883 pattern ≤ (0 : Int) + d1196 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d883, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3908 pattern childGuard
    simpa only [d883, d1196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d883, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3761 pattern childGuard
    simpa only [d883, d1196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3910 (pattern : Twelve) (guard : d1866 pattern = 1) : d891 pattern ≤ (0 : Int) + d1210 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d891, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d891, d1210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d891, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3909 pattern childGuard
    simpa only [d891, d1210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3911 (pattern : Twelve) (guard : d1866 pattern = 1) : d898 pattern ≤ (0 : Int) + d1224 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d898, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3907 pattern childGuard
    simpa only [d898, d1224, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d898, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3910 pattern childGuard
    simpa only [d898, d1224, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3912 (pattern : Twelve) (guard : d1866 pattern = 1) : d877 pattern ≤ (0 : Int) + d674 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d877, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d877, d674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d877, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3879 pattern childGuard
    simpa only [d877, d674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3913 (pattern : Twelve) (guard : d1866 pattern = 1) : d884 pattern ≤ (0 : Int) + d705 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d884, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3912 pattern childGuard
    simpa only [d884, d705, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d884, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3859 pattern childGuard
    simpa only [d884, d705, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3914 (pattern : Twelve) (guard : d1866 pattern = 1) : d892 pattern ≤ (0 : Int) + d731 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d892, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3734 pattern childGuard
    simpa only [d892, d731, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d892, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3913 pattern childGuard
    simpa only [d892, d731, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3915 (pattern : Twelve) (guard : d1866 pattern = 1) : d893 pattern ≤ (0 : Int) + d1211 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d893, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3862 pattern childGuard
    simpa only [d893, d1211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d893, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3909 pattern childGuard
    simpa only [d893, d1211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3916 (pattern : Twelve) (guard : d1866 pattern = 1) : d899 pattern ≤ (0 : Int) + d1225 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d899, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3914 pattern childGuard
    simpa only [d899, d1225, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d899, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3915 pattern childGuard
    simpa only [d899, d1225, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3917 (pattern : Twelve) (guard : d1866 pattern = 1) : d902 pattern ≤ (0 : Int) + d1234 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d902, d1234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3911 pattern childGuard
    simpa only [d902, d1234, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d902, d1234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3916 pattern childGuard
    simpa only [d902, d1234, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3918 (pattern : Twelve) (guard : d1866 pattern = 1) : d878 pattern ≤ (0 : Int) + d1188 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d878, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3848 pattern childGuard
    simpa only [d878, d1188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d878, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3758 pattern childGuard
    simpa only [d878, d1188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3919 (pattern : Twelve) (guard : d1866 pattern = 1) : d885 pattern ≤ (0 : Int) + d1197 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d885, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3912 pattern childGuard
    simpa only [d885, d1197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d885, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3918 pattern childGuard
    simpa only [d885, d1197, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
