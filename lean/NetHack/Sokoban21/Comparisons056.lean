/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons055
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c7840 (pattern : Twelve) (guard : d1866 pattern = 1) : d698 pattern ≤ (0 : Int) + d61 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d698, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7836 pattern childGuard
    simpa only [d698, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d698, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7839 pattern childGuard
    simpa only [d698, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7841 (pattern : Twelve) (guard : d1866 pattern = 1) : d720 pattern ≤ (0 : Int) + d82 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d720, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7833 pattern childGuard
    simpa only [d720, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d720, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7840 pattern childGuard
    simpa only [d720, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7842 (pattern : Twelve) (guard : d1866 pattern = 1) : d741 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d741, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7832 pattern childGuard
    simpa only [d741, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d741, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7841 pattern childGuard
    simpa only [d741, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7843 (pattern : Twelve) (guard : d1866 pattern = 1) : d756 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d756, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7821 pattern childGuard
    simpa only [d756, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d756, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7842 pattern childGuard
    simpa only [d756, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7844 (pattern : Twelve) (guard : d0 pattern = 1) : d5 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7845 (pattern : Twelve) (guard : d1866 pattern = 1) : d633 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1866, d633, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7844 pattern childGuard
    simpa only [d1866, d633, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7846 (pattern : Twelve) (guard : d1866 pattern = 1) : d645 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7845 pattern childGuard
    simpa only [d645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7847 (pattern : Twelve) (guard : d1866 pattern = 1) : d671 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d671, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7846 pattern childGuard
    simpa only [d671, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d671, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d671, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7848 (pattern : Twelve) (guard : d1866 pattern = 1) : d699 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d699, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7847 pattern childGuard
    simpa only [d699, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d699, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7798 pattern childGuard
    simpa only [d699, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7849 (pattern : Twelve) (guard : d1866 pattern = 1) : d721 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d721, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7848 pattern childGuard
    simpa only [d721, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d721, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7802 pattern childGuard
    simpa only [d721, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7850 (pattern : Twelve) (guard : d1866 pattern = 1) : d742 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d742, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7849 pattern childGuard
    simpa only [d742, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d742, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7805 pattern childGuard
    simpa only [d742, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7851 (pattern : Twelve) (guard : d1866 pattern = 1) : d757 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d757, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7850 pattern childGuard
    simpa only [d757, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d757, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d757, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7852 (pattern : Twelve) (guard : d1866 pattern = 1) : d767 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d767, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7843 pattern childGuard
    simpa only [d767, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d767, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7851 pattern childGuard
    simpa only [d767, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7853 (pattern : Twelve) (guard : d1866 pattern = 1) : d772 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d772, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7808 pattern childGuard
    simpa only [d772, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d772, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7852 pattern childGuard
    simpa only [d772, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7854 (pattern : Twelve) (guard : d1866 pattern = 1) : d661 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d661, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d661, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d661, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7736 pattern childGuard
    simpa only [d661, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7855 (pattern : Twelve) (guard : d1866 pattern = 1) : d661 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7854 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7788 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7856 (pattern : Twelve) (guard : d1866 pattern = 1) : d722 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d722, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d722, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d722, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7855 pattern childGuard
    simpa only [d722, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7857 (pattern : Twelve) (guard : d1866 pattern = 1) : d672 pattern ≤ (0 : Int) + d28 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d672, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d672, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d672, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7749 pattern childGuard
    simpa only [d672, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7858 (pattern : Twelve) (guard : d1866 pattern = 1) : d700 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d700, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7857 pattern childGuard
    simpa only [d700, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d700, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7754 pattern childGuard
    simpa only [d700, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7859 (pattern : Twelve) (guard : d1866 pattern = 1) : d723 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d723, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d723, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d723, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7858 pattern childGuard
    simpa only [d723, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7860 (pattern : Twelve) (guard : d1866 pattern = 1) : d743 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d743, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7856 pattern childGuard
    simpa only [d743, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d743, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7859 pattern childGuard
    simpa only [d743, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7861 (pattern : Twelve) (guard : d1866 pattern = 1) : d673 pattern ≤ (0 : Int) + d31 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d673, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d673, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d673, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7766 pattern childGuard
    simpa only [d673, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7862 (pattern : Twelve) (guard : d1866 pattern = 1) : d701 pattern ≤ (0 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7800 pattern childGuard
    simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7861 pattern childGuard
    simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7863 (pattern : Twelve) (guard : d1866 pattern = 1) : d702 pattern ≤ (0 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7800 pattern childGuard
    simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7771 pattern childGuard
    simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7864 (pattern : Twelve) (guard : d1866 pattern = 1) : d724 pattern ≤ (0 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d724, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7862 pattern childGuard
    simpa only [d724, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d724, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7863 pattern childGuard
    simpa only [d724, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7865 (pattern : Twelve) (guard : d1866 pattern = 1) : d703 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d703, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7800 pattern childGuard
    simpa only [d703, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d703, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7774 pattern childGuard
    simpa only [d703, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7866 (pattern : Twelve) (guard : d1866 pattern = 1) : d725 pattern ≤ (0 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d725, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7865 pattern childGuard
    simpa only [d725, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d725, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7778 pattern childGuard
    simpa only [d725, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7867 (pattern : Twelve) (guard : d1866 pattern = 1) : d744 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d744, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7864 pattern childGuard
    simpa only [d744, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d744, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7866 pattern childGuard
    simpa only [d744, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7868 (pattern : Twelve) (guard : d1866 pattern = 1) : d758 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d758, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7860 pattern childGuard
    simpa only [d758, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d758, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7867 pattern childGuard
    simpa only [d758, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7869 (pattern : Twelve) (guard : d1866 pattern = 1) : d726 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d726, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d726, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d726, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7778 pattern childGuard
    simpa only [d726, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7870 (pattern : Twelve) (guard : d1866 pattern = 1) : d745 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d745, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7856 pattern childGuard
    simpa only [d745, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d745, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7869 pattern childGuard
    simpa only [d745, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7871 (pattern : Twelve) (guard : d1866 pattern = 1) : d692 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7804 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7802 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7872 (pattern : Twelve) (guard : d1866 pattern = 1) : d746 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d746, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7871 pattern childGuard
    simpa only [d746, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d746, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7805 pattern childGuard
    simpa only [d746, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7873 (pattern : Twelve) (guard : d1866 pattern = 1) : d759 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d759, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7870 pattern childGuard
    simpa only [d759, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d759, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7872 pattern childGuard
    simpa only [d759, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7874 (pattern : Twelve) (guard : d1866 pattern = 1) : d768 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d768, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7868 pattern childGuard
    simpa only [d768, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d768, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7873 pattern childGuard
    simpa only [d768, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7875 (pattern : Twelve) (guard : d1866 pattern = 1) : d704 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d704, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7800 pattern childGuard
    simpa only [d704, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d704, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7816 pattern childGuard
    simpa only [d704, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7876 (pattern : Twelve) (guard : d1866 pattern = 1) : d727 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d727, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7800 pattern childGuard
    simpa only [d727, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d727, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7875 pattern childGuard
    simpa only [d727, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7877 (pattern : Twelve) (guard : d1866 pattern = 1) : d728 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d728, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7800 pattern childGuard
    simpa only [d728, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d728, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7778 pattern childGuard
    simpa only [d728, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7878 (pattern : Twelve) (guard : d1866 pattern = 1) : d747 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d747, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7876 pattern childGuard
    simpa only [d747, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d747, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7877 pattern childGuard
    simpa only [d747, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7879 (pattern : Twelve) (guard : d1866 pattern = 1) : d697 pattern ≤ (0 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7833 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7831 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7880 (pattern : Twelve) (guard : d1866 pattern = 1) : d748 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d748, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7879 pattern childGuard
    simpa only [d748, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d748, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7841 pattern childGuard
    simpa only [d748, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7881 (pattern : Twelve) (guard : d1866 pattern = 1) : d760 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d760, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7878 pattern childGuard
    simpa only [d760, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d760, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7880 pattern childGuard
    simpa only [d760, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7882 (pattern : Twelve) (guard : d1866 pattern = 1) : d761 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d761, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7872 pattern childGuard
    simpa only [d761, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d761, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d761, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7883 (pattern : Twelve) (guard : d1866 pattern = 1) : d769 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d769, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7881 pattern childGuard
    simpa only [d769, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d769, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7882 pattern childGuard
    simpa only [d769, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7884 (pattern : Twelve) (guard : d1866 pattern = 1) : d773 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d773, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7874 pattern childGuard
    simpa only [d773, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d773, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7883 pattern childGuard
    simpa only [d773, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7885 (pattern : Twelve) (guard : d1866 pattern = 1) : d775 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7853 pattern childGuard
    simpa only [d775, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7884 pattern childGuard
    simpa only [d775, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7886 (pattern : Twelve) (guard : d1866 pattern = 1) : d776 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7885 pattern childGuard
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7884 pattern childGuard
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7887 (pattern : Twelve) (guard : d1866 pattern = 1) : d674 pattern ≤ (0 : Int) + d120 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d674, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d674, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d674, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7838 pattern childGuard
    simpa only [d674, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7888 (pattern : Twelve) (guard : d1866 pattern = 1) : d705 pattern ≤ (0 : Int) + d129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d705, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7887 pattern childGuard
    simpa only [d705, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d705, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7754 pattern childGuard
    simpa only [d705, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7889 (pattern : Twelve) (guard : d1866 pattern = 1) : d729 pattern ≤ (0 : Int) + d136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d729, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d729, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d729, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7888 pattern childGuard
    simpa only [d729, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7890 (pattern : Twelve) (guard : d1866 pattern = 1) : d749 pattern ≤ (0 : Int) + d144 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d749, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7856 pattern childGuard
    simpa only [d749, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d749, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7889 pattern childGuard
    simpa only [d749, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7891 (pattern : Twelve) (guard : d1866 pattern = 1) : d657 pattern ≤ (0 : Int) + d121 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d657, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d657, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d657, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7776 pattern childGuard
    simpa only [d657, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7892 (pattern : Twelve) (guard : d1866 pattern = 1) : d692 pattern ≤ (0 : Int) + d130 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d692, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7891 pattern childGuard
    simpa only [d692, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d692, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7801 pattern childGuard
    simpa only [d692, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7893 (pattern : Twelve) (guard : d1866 pattern = 1) : d730 pattern ≤ (0 : Int) + d137 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d730, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7862 pattern childGuard
    simpa only [d730, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d730, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7892 pattern childGuard
    simpa only [d730, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7894 (pattern : Twelve) (guard : d1866 pattern = 1) : d731 pattern ≤ (0 : Int) + d138 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d731, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7804 pattern childGuard
    simpa only [d731, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d731, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7888 pattern childGuard
    simpa only [d731, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7895 (pattern : Twelve) (guard : d1866 pattern = 1) : d750 pattern ≤ (0 : Int) + d145 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d750, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7893 pattern childGuard
    simpa only [d750, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d750, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7894 pattern childGuard
    simpa only [d750, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7896 (pattern : Twelve) (guard : d1866 pattern = 1) : d762 pattern ≤ (0 : Int) + d149 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d762, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7890 pattern childGuard
    simpa only [d762, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d762, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7895 pattern childGuard
    simpa only [d762, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7897 (pattern : Twelve) (guard : d1866 pattern = 1) : d692 pattern ≤ (0 : Int) + d139 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7804 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7892 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7898 (pattern : Twelve) (guard : d1866 pattern = 1) : d751 pattern ≤ (0 : Int) + d146 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d751, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7897 pattern childGuard
    simpa only [d751, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d751, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7894 pattern childGuard
    simpa only [d751, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7899 (pattern : Twelve) (guard : d1866 pattern = 1) : d763 pattern ≤ (0 : Int) + d150 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d763, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7890 pattern childGuard
    simpa only [d763, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d763, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7898 pattern childGuard
    simpa only [d763, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7900 (pattern : Twelve) (guard : d1866 pattern = 1) : d770 pattern ≤ (0 : Int) + d153 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d770, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7896 pattern childGuard
    simpa only [d770, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d770, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7899 pattern childGuard
    simpa only [d770, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7901 (pattern : Twelve) (guard : d1866 pattern = 1) : d675 pattern ≤ (0 : Int) + d122 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d675, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d675, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d675, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7825 pattern childGuard
    simpa only [d675, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7902 (pattern : Twelve) (guard : d1866 pattern = 1) : d706 pattern ≤ (0 : Int) + d131 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d706, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7891 pattern childGuard
    simpa only [d706, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d706, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7901 pattern childGuard
    simpa only [d706, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7903 (pattern : Twelve) (guard : d1866 pattern = 1) : d732 pattern ≤ (0 : Int) + d140 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d732, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7800 pattern childGuard
    simpa only [d732, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d732, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7902 pattern childGuard
    simpa only [d732, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7904 (pattern : Twelve) (guard : d1866 pattern = 1) : d666 pattern ≤ (0 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d666, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d666, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d666, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7815 pattern childGuard
    simpa only [d666, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7905 (pattern : Twelve) (guard : d1866 pattern = 1) : d704 pattern ≤ (0 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d704, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7800 pattern childGuard
    simpa only [d704, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d704, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7904 pattern childGuard
    simpa only [d704, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7906 (pattern : Twelve) (guard : d1866 pattern = 1) : d733 pattern ≤ (0 : Int) + d141 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d733, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7905 pattern childGuard
    simpa only [d733, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d733, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7888 pattern childGuard
    simpa only [d733, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7907 (pattern : Twelve) (guard : d1866 pattern = 1) : d752 pattern ≤ (0 : Int) + d147 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d752, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7903 pattern childGuard
    simpa only [d752, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d752, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7906 pattern childGuard
    simpa only [d752, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7908 (pattern : Twelve) (guard : d1866 pattern = 1) : d14 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3017 pattern childGuard
    simpa only [d1866, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5335 pattern childGuard
    simpa only [d1866, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7909 (pattern : Twelve) (guard : d1866 pattern = 1) : d14 pattern ≤ (0 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7908 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3828 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7910 (pattern : Twelve) (guard : d1866 pattern = 1) : d676 pattern ≤ (0 : Int) + d124 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d676, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d676, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d676, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7909 pattern childGuard
    simpa only [d676, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7911 (pattern : Twelve) (guard : d1866 pattern = 1) : d159 pattern ≤ (0 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d159, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d1866, d159, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d159, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d1866, d159, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7912 (pattern : Twelve) (guard : d1866 pattern = 1) : d159 pattern ≤ (0 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7815 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7911 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7913 (pattern : Twelve) (guard : d1866 pattern = 1) : d677 pattern ≤ (0 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d677, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7912 pattern childGuard
    simpa only [d677, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d677, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d677, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7914 (pattern : Twelve) (guard : d1866 pattern = 1) : d707 pattern ≤ (0 : Int) + d133 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d707, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7910 pattern childGuard
    simpa only [d707, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d707, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7913 pattern childGuard
    simpa only [d707, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7915 (pattern : Twelve) (guard : d1866 pattern = 1) : d734 pattern ≤ (0 : Int) + d142 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d734, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7833 pattern childGuard
    simpa only [d734, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d734, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7914 pattern childGuard
    simpa only [d734, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7916 (pattern : Twelve) (guard : d1866 pattern = 1) : d676 pattern ≤ (0 : Int) + d126 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d676, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d676, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d676, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7908 pattern childGuard
    simpa only [d676, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7917 (pattern : Twelve) (guard : d1866 pattern = 1) : d677 pattern ≤ (0 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d677, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7815 pattern childGuard
    simpa only [d677, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d677, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d677, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7918 (pattern : Twelve) (guard : d1866 pattern = 1) : d707 pattern ≤ (0 : Int) + d134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d707, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7916 pattern childGuard
    simpa only [d707, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d707, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7917 pattern childGuard
    simpa only [d707, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7919 (pattern : Twelve) (guard : d1866 pattern = 1) : d678 pattern ≤ (0 : Int) + d127 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d678, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7776 pattern childGuard
    simpa only [d678, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d678, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3706 pattern childGuard
    simpa only [d678, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7920 (pattern : Twelve) (guard : d1866 pattern = 1) : d679 pattern ≤ (0 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d679, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7766 pattern childGuard
    simpa only [d679, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d679, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d679, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7921 (pattern : Twelve) (guard : d1866 pattern = 1) : d708 pattern ≤ (0 : Int) + d135 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d708, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7919 pattern childGuard
    simpa only [d708, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d708, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7920 pattern childGuard
    simpa only [d708, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7922 (pattern : Twelve) (guard : d1866 pattern = 1) : d735 pattern ≤ (0 : Int) + d143 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d735, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7918 pattern childGuard
    simpa only [d735, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d735, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7921 pattern childGuard
    simpa only [d735, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7923 (pattern : Twelve) (guard : d1866 pattern = 1) : d753 pattern ≤ (0 : Int) + d148 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d753, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7915 pattern childGuard
    simpa only [d753, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d753, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7922 pattern childGuard
    simpa only [d753, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7924 (pattern : Twelve) (guard : d1866 pattern = 1) : d764 pattern ≤ (0 : Int) + d151 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d764, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7907 pattern childGuard
    simpa only [d764, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d764, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7923 pattern childGuard
    simpa only [d764, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7925 (pattern : Twelve) (guard : d1866 pattern = 1) : d765 pattern ≤ (0 : Int) + d152 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d765, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7898 pattern childGuard
    simpa only [d765, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d765, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d765, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7926 (pattern : Twelve) (guard : d1866 pattern = 1) : d771 pattern ≤ (0 : Int) + d154 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d771, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7924 pattern childGuard
    simpa only [d771, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d771, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7925 pattern childGuard
    simpa only [d771, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7927 (pattern : Twelve) (guard : d1866 pattern = 1) : d774 pattern ≤ (0 : Int) + d155 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d774, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7900 pattern childGuard
    simpa only [d774, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d774, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7926 pattern childGuard
    simpa only [d774, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7928 (pattern : Twelve) (guard : d1866 pattern = 1) : d777 pattern ≤ (0 : Int) + d156 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d777, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7886 pattern childGuard
    simpa only [d777, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d777, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7927 pattern childGuard
    simpa only [d777, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7929 (pattern : Twelve) (guard : d1866 pattern = 1) : d636 pattern ≤ (0 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d636, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7739 pattern childGuard
    simpa only [d636, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d636, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7736 pattern childGuard
    simpa only [d636, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7930 (pattern : Twelve) (guard : d1866 pattern = 1) : d1183 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1183, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7929 pattern childGuard
    simpa only [d1183, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1183, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7736 pattern childGuard
    simpa only [d1183, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7931 (pattern : Twelve) (guard : d1866 pattern = 1) : d1189 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1189, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7741 pattern childGuard
    simpa only [d1189, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1189, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7930 pattern childGuard
    simpa only [d1189, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7932 (pattern : Twelve) (guard : d1866 pattern = 1) : d1199 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1199, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7746 pattern childGuard
    simpa only [d1199, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1199, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7931 pattern childGuard
    simpa only [d1199, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7933 (pattern : Twelve) (guard : d1866 pattern = 1) : d649 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7740 pattern childGuard
    simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7934 (pattern : Twelve) (guard : d1866 pattern = 1) : d1190 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7933 pattern childGuard
    simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7935 (pattern : Twelve) (guard : d1866 pattern = 1) : d1184 pattern ≤ (0 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1184, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7753 pattern childGuard
    simpa only [d1184, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1184, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7838 pattern childGuard
    simpa only [d1184, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7936 (pattern : Twelve) (guard : d1866 pattern = 1) : d1191 pattern ≤ (0 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1191, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7935 pattern childGuard
    simpa only [d1191, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1191, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7839 pattern childGuard
    simpa only [d1191, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7937 (pattern : Twelve) (guard : d1866 pattern = 1) : d1200 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1200, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7934 pattern childGuard
    simpa only [d1200, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1200, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7936 pattern childGuard
    simpa only [d1200, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7938 (pattern : Twelve) (guard : d1866 pattern = 1) : d1216 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1216, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7932 pattern childGuard
    simpa only [d1216, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1216, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7937 pattern childGuard
    simpa only [d1216, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7939 (pattern : Twelve) (guard : d1866 pattern = 1) : d1192 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1192, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7769 pattern childGuard
    simpa only [d1192, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1192, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7798 pattern childGuard
    simpa only [d1192, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7940 (pattern : Twelve) (guard : d1866 pattern = 1) : d651 pattern ≤ (0 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d651, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7929 pattern childGuard
    simpa only [d651, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d651, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d651, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7941 (pattern : Twelve) (guard : d1866 pattern = 1) : d687 pattern ≤ (0 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d687, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7777 pattern childGuard
    simpa only [d687, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d687, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7940 pattern childGuard
    simpa only [d687, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7942 (pattern : Twelve) (guard : d1866 pattern = 1) : d1201 pattern ≤ (0 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1201, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7939 pattern childGuard
    simpa only [d1201, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1201, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7941 pattern childGuard
    simpa only [d1201, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7943 (pattern : Twelve) (guard : d1866 pattern = 1) : d692 pattern ≤ (0 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d692, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7777 pattern childGuard
    simpa only [d692, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d692, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7801 pattern childGuard
    simpa only [d692, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7944 (pattern : Twelve) (guard : d1866 pattern = 1) : d1202 pattern ≤ (0 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1202, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7943 pattern childGuard
    simpa only [d1202, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1202, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7936 pattern childGuard
    simpa only [d1202, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7945 (pattern : Twelve) (guard : d1866 pattern = 1) : d1217 pattern ≤ (0 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1217, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7942 pattern childGuard
    simpa only [d1217, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1217, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7944 pattern childGuard
    simpa only [d1217, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7946 (pattern : Twelve) (guard : d1866 pattern = 1) : d1228 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1228, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7938 pattern childGuard
    simpa only [d1228, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1228, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7945 pattern childGuard
    simpa only [d1228, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7947 (pattern : Twelve) (guard : d1866 pattern = 1) : d1193 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1193, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7788 pattern childGuard
    simpa only [d1193, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1193, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7930 pattern childGuard
    simpa only [d1193, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7948 (pattern : Twelve) (guard : d1866 pattern = 1) : d1203 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1203, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7791 pattern childGuard
    simpa only [d1203, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1203, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7947 pattern childGuard
    simpa only [d1203, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7949 (pattern : Twelve) (guard : d1866 pattern = 1) : d1204 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1204, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d1204, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1204, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7936 pattern childGuard
    simpa only [d1204, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7950 (pattern : Twelve) (guard : d1866 pattern = 1) : d1218 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1218, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7948 pattern childGuard
    simpa only [d1218, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1218, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7949 pattern childGuard
    simpa only [d1218, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7951 (pattern : Twelve) (guard : d1866 pattern = 1) : d716 pattern ≤ (0 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d716, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7804 pattern childGuard
    simpa only [d716, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d716, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7941 pattern childGuard
    simpa only [d716, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7952 (pattern : Twelve) (guard : d1866 pattern = 1) : d1219 pattern ≤ (0 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1219, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7951 pattern childGuard
    simpa only [d1219, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1219, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7944 pattern childGuard
    simpa only [d1219, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7953 (pattern : Twelve) (guard : d1866 pattern = 1) : d1229 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1229, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7950 pattern childGuard
    simpa only [d1229, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1229, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7952 pattern childGuard
    simpa only [d1229, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7954 (pattern : Twelve) (guard : d1866 pattern = 1) : d1237 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7946 pattern childGuard
    simpa only [d1237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7953 pattern childGuard
    simpa only [d1237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7955 (pattern : Twelve) (guard : d1866 pattern = 1) : d1185 pattern ≤ (0 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1185, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7929 pattern childGuard
    simpa only [d1185, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1185, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7815 pattern childGuard
    simpa only [d1185, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7956 (pattern : Twelve) (guard : d1866 pattern = 1) : d1194 pattern ≤ (0 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1194, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7777 pattern childGuard
    simpa only [d1194, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1194, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7955 pattern childGuard
    simpa only [d1194, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7957 (pattern : Twelve) (guard : d1866 pattern = 1) : d1205 pattern ≤ (0 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1205, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7819 pattern childGuard
    simpa only [d1205, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1205, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7956 pattern childGuard
    simpa only [d1205, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7958 (pattern : Twelve) (guard : d1866 pattern = 1) : d1206 pattern ≤ (0 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1206, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7777 pattern childGuard
    simpa only [d1206, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1206, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7936 pattern childGuard
    simpa only [d1206, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7959 (pattern : Twelve) (guard : d1866 pattern = 1) : d1220 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1220, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7957 pattern childGuard
    simpa only [d1220, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1220, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7958 pattern childGuard
    simpa only [d1220, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7960 (pattern : Twelve) (guard : d1866 pattern = 1) : d644 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d644, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7748 pattern childGuard
    simpa only [d644, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d644, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7815 pattern childGuard
    simpa only [d644, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7961 (pattern : Twelve) (guard : d1866 pattern = 1) : d670 pattern ≤ (0 : Int) + d820 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d670, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7960 pattern childGuard
    simpa only [d670, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d670, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d670, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7962 (pattern : Twelve) (guard : d1866 pattern = 1) : d698 pattern ≤ (0 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d698, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7836 pattern childGuard
    simpa only [d698, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d698, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7961 pattern childGuard
    simpa only [d698, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7963 (pattern : Twelve) (guard : d1866 pattern = 1) : d720 pattern ≤ (0 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d720, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7833 pattern childGuard
    simpa only [d720, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d720, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7962 pattern childGuard
    simpa only [d720, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7964 (pattern : Twelve) (guard : d1866 pattern = 1) : d697 pattern ≤ (0 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d697, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7836 pattern childGuard
    simpa only [d697, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d697, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7830 pattern childGuard
    simpa only [d697, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7965 (pattern : Twelve) (guard : d1866 pattern = 1) : d1186 pattern ≤ (0 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1186, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7838 pattern childGuard
    simpa only [d1186, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1186, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3702 pattern childGuard
    simpa only [d1186, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7966 (pattern : Twelve) (guard : d1866 pattern = 1) : d1195 pattern ≤ (0 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1195, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7965 pattern childGuard
    simpa only [d1195, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1195, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3885 pattern childGuard
    simpa only [d1195, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7967 (pattern : Twelve) (guard : d1866 pattern = 1) : d1207 pattern ≤ (0 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1207, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7964 pattern childGuard
    simpa only [d1207, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1207, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7966 pattern childGuard
    simpa only [d1207, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7968 (pattern : Twelve) (guard : d1866 pattern = 1) : d1221 pattern ≤ (0 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1221, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7963 pattern childGuard
    simpa only [d1221, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1221, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7967 pattern childGuard
    simpa only [d1221, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7969 (pattern : Twelve) (guard : d1866 pattern = 1) : d1230 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1230, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7959 pattern childGuard
    simpa only [d1230, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1230, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7968 pattern childGuard
    simpa only [d1230, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7970 (pattern : Twelve) (guard : d1866 pattern = 1) : d1231 pattern ≤ (0 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1231, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7952 pattern childGuard
    simpa only [d1231, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1231, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1231, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7971 (pattern : Twelve) (guard : d1866 pattern = 1) : d1238 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1238, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7969 pattern childGuard
    simpa only [d1238, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1238, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7970 pattern childGuard
    simpa only [d1238, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7972 (pattern : Twelve) (guard : d1866 pattern = 1) : d1241 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1241, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7954 pattern childGuard
    simpa only [d1241, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1241, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7971 pattern childGuard
    simpa only [d1241, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7973 (pattern : Twelve) (guard : d1866 pattern = 1) : d1208 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1208, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d1208, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1208, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7947 pattern childGuard
    simpa only [d1208, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7974 (pattern : Twelve) (guard : d1866 pattern = 1) : d1222 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1222, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7973 pattern childGuard
    simpa only [d1222, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1222, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7949 pattern childGuard
    simpa only [d1222, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7975 (pattern : Twelve) (guard : d1866 pattern = 1) : d1232 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1232, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7974 pattern childGuard
    simpa only [d1232, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1232, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7952 pattern childGuard
    simpa only [d1232, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7976 (pattern : Twelve) (guard : d1866 pattern = 1) : d1209 pattern ≤ (0 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1209, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7800 pattern childGuard
    simpa only [d1209, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1209, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7956 pattern childGuard
    simpa only [d1209, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7977 (pattern : Twelve) (guard : d1866 pattern = 1) : d1223 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1223, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7976 pattern childGuard
    simpa only [d1223, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1223, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7958 pattern childGuard
    simpa only [d1223, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7978 (pattern : Twelve) (guard : d1866 pattern = 1) : d1233 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1233, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7977 pattern childGuard
    simpa only [d1233, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1233, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7968 pattern childGuard
    simpa only [d1233, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7979 (pattern : Twelve) (guard : d1866 pattern = 1) : d1239 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1239, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7978 pattern childGuard
    simpa only [d1239, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1239, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7970 pattern childGuard
    simpa only [d1239, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
