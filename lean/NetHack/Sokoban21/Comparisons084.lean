/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons083
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c11760 (pattern : Twelve) (guard : d0 pattern = 1) : d437 pattern ≤ (1 : Int) + d840 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11761 (pattern : Twelve) (guard : d1999 pattern = 1) : d450 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11760 pattern childGuard
    simpa only [d1999, d450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11746 pattern childGuard
    simpa only [d1999, d450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11762 (pattern : Twelve) (guard : d1999 pattern = 1) : d6 pattern ≤ (1 : Int) + d6 pattern := by
  omega
theorem c11763 (pattern : Twelve) (guard : d1999 pattern = 1) : d458 pattern ≤ (1 : Int) + d2002 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d458, d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11761 pattern childGuard
    simpa only [d458, d2002, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d458, d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11762 pattern childGuard
    simpa only [d458, d2002, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11764 (pattern : Twelve) (guard : d1999 pattern = 1) : d466 pattern ≤ (1 : Int) + d2003 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d466, d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11759 pattern childGuard
    simpa only [d466, d2003, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d466, d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11763 pattern childGuard
    simpa only [d466, d2003, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11765 (pattern : Twelve) (guard : d1999 pattern = 1) : d471 pattern ≤ (1 : Int) + d2004 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d471, d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11749 pattern childGuard
    simpa only [d471, d2004, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d471, d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11764 pattern childGuard
    simpa only [d471, d2004, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11766 (pattern : Twelve) (guard : d0 pattern = 1) : d438 pattern ≤ (1 : Int) + d838 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11767 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d824 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11768 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (1 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d438, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1852, d438, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d438, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11767 pattern childGuard
    simpa only [d1852, d438, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11769 (pattern : Twelve) (guard : d1999 pattern = 1) : d438 pattern ≤ (1 : Int) + d838 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11766 pattern childGuard
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11768 pattern childGuard
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11770 (pattern : Twelve) (guard : d0 pattern = 1) : d439 pattern ≤ (1 : Int) + d847 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11771 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d832 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11772 (pattern : Twelve) (guard : d1852 pattern = 1) : d440 pattern ≤ (1 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d440, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11734 pattern childGuard
    simpa only [d1852, d440, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d440, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11771 pattern childGuard
    simpa only [d1852, d440, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11773 (pattern : Twelve) (guard : d1999 pattern = 1) : d451 pattern ≤ (1 : Int) + d847 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11770 pattern childGuard
    simpa only [d1999, d451, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11772 pattern childGuard
    simpa only [d1999, d451, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11774 (pattern : Twelve) (guard : d1999 pattern = 1) : d459 pattern ≤ (1 : Int) + d2005 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d459, d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11769 pattern childGuard
    simpa only [d459, d2005, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d459, d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11773 pattern childGuard
    simpa only [d459, d2005, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11775 (pattern : Twelve) (guard : d0 pattern = 1) : d432 pattern ≤ (1 : Int) + d847 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11776 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (1 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d432, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11744 pattern childGuard
    simpa only [d1852, d432, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d432, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11771 pattern childGuard
    simpa only [d1852, d432, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11777 (pattern : Twelve) (guard : d1999 pattern = 1) : d432 pattern ≤ (1 : Int) + d847 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11775 pattern childGuard
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11776 pattern childGuard
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11778 (pattern : Twelve) (guard : d1999 pattern = 1) : d460 pattern ≤ (1 : Int) + d2005 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d460, d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11769 pattern childGuard
    simpa only [d460, d2005, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d460, d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11777 pattern childGuard
    simpa only [d460, d2005, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11779 (pattern : Twelve) (guard : d1999 pattern = 1) : d467 pattern ≤ (1 : Int) + d2005 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11774 pattern childGuard
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11778 pattern childGuard
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11780 (pattern : Twelve) (guard : d0 pattern = 1) : d441 pattern ≤ (1 : Int) + d849 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11781 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d834 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11782 (pattern : Twelve) (guard : d1852 pattern = 1) : d441 pattern ≤ (1 : Int) + d849 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d441, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d1852, d441, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d441, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11781 pattern childGuard
    simpa only [d1852, d441, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11783 (pattern : Twelve) (guard : d1999 pattern = 1) : d441 pattern ≤ (1 : Int) + d849 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11780 pattern childGuard
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11782 pattern childGuard
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11784 (pattern : Twelve) (guard : d0 pattern = 1) : d436 pattern ≤ (1 : Int) + d851 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11785 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d836 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11786 (pattern : Twelve) (guard : d1852 pattern = 1) : d436 pattern ≤ (1 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d436, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11755 pattern childGuard
    simpa only [d1852, d436, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d436, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11785 pattern childGuard
    simpa only [d1852, d436, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11787 (pattern : Twelve) (guard : d1999 pattern = 1) : d436 pattern ≤ (1 : Int) + d851 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11784 pattern childGuard
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11786 pattern childGuard
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11788 (pattern : Twelve) (guard : d1999 pattern = 1) : d461 pattern ≤ (1 : Int) + d2006 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d461, d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11783 pattern childGuard
    simpa only [d461, d2006, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d461, d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11787 pattern childGuard
    simpa only [d461, d2006, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11789 (pattern : Twelve) (guard : d1999 pattern = 1) : d462 pattern ≤ (1 : Int) + d2007 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d462, d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11777 pattern childGuard
    simpa only [d462, d2007, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d462, d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11762 pattern childGuard
    simpa only [d462, d2007, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11790 (pattern : Twelve) (guard : d1999 pattern = 1) : d468 pattern ≤ (1 : Int) + d2008 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d468, d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11788 pattern childGuard
    simpa only [d468, d2008, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d468, d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11789 pattern childGuard
    simpa only [d468, d2008, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11791 (pattern : Twelve) (guard : d1999 pattern = 1) : d472 pattern ≤ (1 : Int) + d2009 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d472, d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11779 pattern childGuard
    simpa only [d472, d2009, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d472, d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11790 pattern childGuard
    simpa only [d472, d2009, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11792 (pattern : Twelve) (guard : d1999 pattern = 1) : d474 pattern ≤ (1 : Int) + d2010 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d474, d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11765 pattern childGuard
    simpa only [d474, d2010, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d474, d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11791 pattern childGuard
    simpa only [d474, d2010, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11793 (pattern : Twelve) (guard : d0 pattern = 1) : d439 pattern ≤ (1 : Int) + d840 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11794 (pattern : Twelve) (guard : d1852 pattern = 1) : d440 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d440, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11734 pattern childGuard
    simpa only [d1852, d440, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d440, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11745 pattern childGuard
    simpa only [d1852, d440, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11795 (pattern : Twelve) (guard : d1999 pattern = 1) : d451 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11793 pattern childGuard
    simpa only [d1999, d451, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11794 pattern childGuard
    simpa only [d1999, d451, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11796 (pattern : Twelve) (guard : d1999 pattern = 1) : d459 pattern ≤ (1 : Int) + d2000 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d459, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11769 pattern childGuard
    simpa only [d459, d2000, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d459, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11795 pattern childGuard
    simpa only [d459, d2000, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11797 (pattern : Twelve) (guard : d0 pattern = 1) : d432 pattern ≤ (1 : Int) + d840 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11798 (pattern : Twelve) (guard : d1999 pattern = 1) : d432 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11797 pattern childGuard
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11746 pattern childGuard
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11799 (pattern : Twelve) (guard : d1999 pattern = 1) : d460 pattern ≤ (1 : Int) + d2000 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d460, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11769 pattern childGuard
    simpa only [d460, d2000, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d460, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11798 pattern childGuard
    simpa only [d460, d2000, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11800 (pattern : Twelve) (guard : d1999 pattern = 1) : d467 pattern ≤ (1 : Int) + d2000 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11796 pattern childGuard
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11799 pattern childGuard
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11801 (pattern : Twelve) (guard : d0 pattern = 1) : d441 pattern ≤ (1 : Int) + d842 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11802 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d828 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11803 (pattern : Twelve) (guard : d1852 pattern = 1) : d441 pattern ≤ (1 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d441, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d1852, d441, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d441, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11802 pattern childGuard
    simpa only [d1852, d441, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11804 (pattern : Twelve) (guard : d1999 pattern = 1) : d441 pattern ≤ (1 : Int) + d842 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11801 pattern childGuard
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11803 pattern childGuard
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11805 (pattern : Twelve) (guard : d0 pattern = 1) : d436 pattern ≤ (1 : Int) + d844 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11806 (pattern : Twelve) (guard : d1999 pattern = 1) : d436 pattern ≤ (1 : Int) + d844 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11805 pattern childGuard
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11757 pattern childGuard
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11807 (pattern : Twelve) (guard : d1999 pattern = 1) : d461 pattern ≤ (1 : Int) + d2001 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d461, d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11804 pattern childGuard
    simpa only [d461, d2001, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d461, d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11806 pattern childGuard
    simpa only [d461, d2001, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11808 (pattern : Twelve) (guard : d1999 pattern = 1) : d462 pattern ≤ (1 : Int) + d2002 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d462, d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11798 pattern childGuard
    simpa only [d462, d2002, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d462, d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11762 pattern childGuard
    simpa only [d462, d2002, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11809 (pattern : Twelve) (guard : d1999 pattern = 1) : d468 pattern ≤ (1 : Int) + d2003 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d468, d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11807 pattern childGuard
    simpa only [d468, d2003, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d468, d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11808 pattern childGuard
    simpa only [d468, d2003, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11810 (pattern : Twelve) (guard : d1999 pattern = 1) : d472 pattern ≤ (1 : Int) + d2004 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d472, d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11800 pattern childGuard
    simpa only [d472, d2004, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d472, d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11809 pattern childGuard
    simpa only [d472, d2004, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11811 (pattern : Twelve) (guard : d1999 pattern = 1) : d472 pattern ≤ (1 : Int) + d2010 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11810 pattern childGuard
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11791 pattern childGuard
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11812 (pattern : Twelve) (guard : d1999 pattern = 1) : d475 pattern ≤ (1 : Int) + d2010 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11792 pattern childGuard
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11811 pattern childGuard
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11813 (pattern : Twelve) (guard : d1999 pattern = 1) : d452 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11793 pattern childGuard
    simpa only [d1999, d452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11746 pattern childGuard
    simpa only [d1999, d452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11814 (pattern : Twelve) (guard : d1999 pattern = 1) : d463 pattern ≤ (1 : Int) + d2000 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d463, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11769 pattern childGuard
    simpa only [d463, d2000, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d463, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11813 pattern childGuard
    simpa only [d463, d2000, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11815 (pattern : Twelve) (guard : d1999 pattern = 1) : d469 pattern ≤ (1 : Int) + d2000 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11814 pattern childGuard
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11799 pattern childGuard
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11816 (pattern : Twelve) (guard : d1 pattern = 1) : d123 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d123, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d123, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d123, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d123, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11817 (pattern : Twelve) (guard : d1 pattern = 1) : d132 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11816 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11818 (pattern : Twelve) (guard : d1852 pattern = 1) : d442 pattern ≤ (1 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d442, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11817 pattern childGuard
    simpa only [d1852, d442, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d442, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11802 pattern childGuard
    simpa only [d1852, d442, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11819 (pattern : Twelve) (guard : d1999 pattern = 1) : d453 pattern ≤ (1 : Int) + d842 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11801 pattern childGuard
    simpa only [d1999, d453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11818 pattern childGuard
    simpa only [d1999, d453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11820 (pattern : Twelve) (guard : d1 pattern = 1) : d126 pattern ≤ (1 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d126, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d126, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d126, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11195 pattern childGuard
    simpa only [d126, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11821 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (1 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d47, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d47, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11822 (pattern : Twelve) (guard : d1 pattern = 1) : d134 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d134, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11820 pattern childGuard
    simpa only [d134, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d134, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11821 pattern childGuard
    simpa only [d134, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11823 (pattern : Twelve) (guard : d1852 pattern = 1) : d443 pattern ≤ (1 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d443, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11822 pattern childGuard
    simpa only [d1852, d443, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d443, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11756 pattern childGuard
    simpa only [d1852, d443, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11824 (pattern : Twelve) (guard : d1999 pattern = 1) : d454 pattern ≤ (1 : Int) + d844 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11805 pattern childGuard
    simpa only [d1999, d454, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11823 pattern childGuard
    simpa only [d1999, d454, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11825 (pattern : Twelve) (guard : d1999 pattern = 1) : d464 pattern ≤ (1 : Int) + d2001 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d464, d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11819 pattern childGuard
    simpa only [d464, d2001, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d464, d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11824 pattern childGuard
    simpa only [d464, d2001, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11826 (pattern : Twelve) (guard : d1999 pattern = 1) : d470 pattern ≤ (1 : Int) + d2003 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d470, d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11825 pattern childGuard
    simpa only [d470, d2003, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d470, d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11808 pattern childGuard
    simpa only [d470, d2003, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11827 (pattern : Twelve) (guard : d1999 pattern = 1) : d473 pattern ≤ (1 : Int) + d2004 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d473, d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11815 pattern childGuard
    simpa only [d473, d2004, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d473, d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11826 pattern childGuard
    simpa only [d473, d2004, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11828 (pattern : Twelve) (guard : d1999 pattern = 1) : d452 pattern ≤ (1 : Int) + d847 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11770 pattern childGuard
    simpa only [d1999, d452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11776 pattern childGuard
    simpa only [d1999, d452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11829 (pattern : Twelve) (guard : d1999 pattern = 1) : d463 pattern ≤ (1 : Int) + d2005 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d463, d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11769 pattern childGuard
    simpa only [d463, d2005, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d463, d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11828 pattern childGuard
    simpa only [d463, d2005, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11830 (pattern : Twelve) (guard : d1999 pattern = 1) : d469 pattern ≤ (1 : Int) + d2005 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11829 pattern childGuard
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11778 pattern childGuard
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11831 (pattern : Twelve) (guard : d1852 pattern = 1) : d442 pattern ≤ (1 : Int) + d849 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d442, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11817 pattern childGuard
    simpa only [d1852, d442, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d442, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11781 pattern childGuard
    simpa only [d1852, d442, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11832 (pattern : Twelve) (guard : d1999 pattern = 1) : d453 pattern ≤ (1 : Int) + d849 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11780 pattern childGuard
    simpa only [d1999, d453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11831 pattern childGuard
    simpa only [d1999, d453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11833 (pattern : Twelve) (guard : d1852 pattern = 1) : d443 pattern ≤ (1 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d443, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11822 pattern childGuard
    simpa only [d1852, d443, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d443, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11785 pattern childGuard
    simpa only [d1852, d443, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11834 (pattern : Twelve) (guard : d1999 pattern = 1) : d454 pattern ≤ (1 : Int) + d851 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11784 pattern childGuard
    simpa only [d1999, d454, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11833 pattern childGuard
    simpa only [d1999, d454, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11835 (pattern : Twelve) (guard : d1999 pattern = 1) : d464 pattern ≤ (1 : Int) + d2006 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d464, d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11832 pattern childGuard
    simpa only [d464, d2006, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d464, d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11834 pattern childGuard
    simpa only [d464, d2006, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11836 (pattern : Twelve) (guard : d1999 pattern = 1) : d470 pattern ≤ (1 : Int) + d2008 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d470, d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11835 pattern childGuard
    simpa only [d470, d2008, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d470, d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11789 pattern childGuard
    simpa only [d470, d2008, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11837 (pattern : Twelve) (guard : d1999 pattern = 1) : d473 pattern ≤ (1 : Int) + d2009 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d473, d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11830 pattern childGuard
    simpa only [d473, d2009, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d473, d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11836 pattern childGuard
    simpa only [d473, d2009, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11838 (pattern : Twelve) (guard : d1999 pattern = 1) : d473 pattern ≤ (1 : Int) + d2010 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11827 pattern childGuard
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11837 pattern childGuard
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11839 (pattern : Twelve) (guard : d1999 pattern = 1) : d476 pattern ≤ (1 : Int) + d2010 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11812 pattern childGuard
    simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11838 pattern childGuard
    simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11840 (pattern : Twelve) (guard : d0 pattern = 1) : d426 pattern ≤ (1 : Int) + d1293 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11841 (pattern : Twelve) (guard : d0 pattern = 1) : d908 pattern ≤ (1 : Int) + d1284 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11842 (pattern : Twelve) (guard : d1852 pattern = 1) : d1070 pattern ≤ (1 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1070, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1852, d1070, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1070, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11841 pattern childGuard
    simpa only [d1852, d1070, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11843 (pattern : Twelve) (guard : d1999 pattern = 1) : d1078 pattern ≤ (1 : Int) + d1293 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11840 pattern childGuard
    simpa only [d1999, d1078, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11842 pattern childGuard
    simpa only [d1999, d1078, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11844 (pattern : Twelve) (guard : d0 pattern = 1) : d1071 pattern ≤ (1 : Int) + d1295 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11845 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (1 : Int) + d827 pattern := by
  omega
theorem c11846 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11847 (pattern : Twelve) (guard : d1852 pattern = 1) : d1072 pattern ≤ (1 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1072, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11845 pattern childGuard
    simpa only [d1852, d1072, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1072, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11846 pattern childGuard
    simpa only [d1852, d1072, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11848 (pattern : Twelve) (guard : d1999 pattern = 1) : d1079 pattern ≤ (1 : Int) + d1295 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11844 pattern childGuard
    simpa only [d1999, d1079, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11847 pattern childGuard
    simpa only [d1999, d1079, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11849 (pattern : Twelve) (guard : d1999 pattern = 1) : d1088 pattern ≤ (1 : Int) + d2011 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1088, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11843 pattern childGuard
    simpa only [d1088, d2011, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1088, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11848 pattern childGuard
    simpa only [d1088, d2011, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11850 (pattern : Twelve) (guard : d0 pattern = 1) : d430 pattern ≤ (1 : Int) + d1293 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11851 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1284 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11852 (pattern : Twelve) (guard : d1852 pattern = 1) : d1073 pattern ≤ (1 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1073, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1852, d1073, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1073, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11851 pattern childGuard
    simpa only [d1852, d1073, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11853 (pattern : Twelve) (guard : d1999 pattern = 1) : d1080 pattern ≤ (1 : Int) + d1293 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11850 pattern childGuard
    simpa only [d1999, d1080, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11852 pattern childGuard
    simpa only [d1999, d1080, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11854 (pattern : Twelve) (guard : d0 pattern = 1) : d432 pattern ≤ (1 : Int) + d1295 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11855 (pattern : Twelve) (guard : d1999 pattern = 1) : d1081 pattern ≤ (1 : Int) + d1295 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11854 pattern childGuard
    simpa only [d1999, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11847 pattern childGuard
    simpa only [d1999, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11856 (pattern : Twelve) (guard : d1999 pattern = 1) : d1089 pattern ≤ (1 : Int) + d2011 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1089, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11853 pattern childGuard
    simpa only [d1089, d2011, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1089, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11855 pattern childGuard
    simpa only [d1089, d2011, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11857 (pattern : Twelve) (guard : d1999 pattern = 1) : d1095 pattern ≤ (1 : Int) + d2011 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11849 pattern childGuard
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11856 pattern childGuard
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11858 (pattern : Twelve) (guard : d0 pattern = 1) : d434 pattern ≤ (1 : Int) + d1297 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11859 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (1 : Int) + d34 pattern := by
  omega
theorem c11860 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11861 (pattern : Twelve) (guard : d1852 pattern = 1) : d1074 pattern ≤ (1 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1074, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11859 pattern childGuard
    simpa only [d1852, d1074, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1074, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11860 pattern childGuard
    simpa only [d1852, d1074, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11862 (pattern : Twelve) (guard : d1999 pattern = 1) : d1082 pattern ≤ (1 : Int) + d1297 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11858 pattern childGuard
    simpa only [d1999, d1082, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11861 pattern childGuard
    simpa only [d1999, d1082, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11863 (pattern : Twelve) (guard : d0 pattern = 1) : d436 pattern ≤ (1 : Int) + d1299 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11864 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (1 : Int) + d830 pattern := by
  omega
theorem c11865 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1288 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11866 (pattern : Twelve) (guard : d1852 pattern = 1) : d1075 pattern ≤ (1 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1075, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11864 pattern childGuard
    simpa only [d1852, d1075, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1075, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11865 pattern childGuard
    simpa only [d1852, d1075, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11867 (pattern : Twelve) (guard : d1999 pattern = 1) : d1083 pattern ≤ (1 : Int) + d1299 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11863 pattern childGuard
    simpa only [d1999, d1083, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11866 pattern childGuard
    simpa only [d1999, d1083, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11868 (pattern : Twelve) (guard : d1999 pattern = 1) : d1090 pattern ≤ (1 : Int) + d2012 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1090, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11862 pattern childGuard
    simpa only [d1090, d2012, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1090, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11867 pattern childGuard
    simpa only [d1090, d2012, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11869 (pattern : Twelve) (guard : d1999 pattern = 1) : d1091 pattern ≤ (1 : Int) + d2013 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1091, d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11855 pattern childGuard
    simpa only [d1091, d2013, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1091, d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11762 pattern childGuard
    simpa only [d1091, d2013, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11870 (pattern : Twelve) (guard : d1999 pattern = 1) : d1096 pattern ≤ (1 : Int) + d2014 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1096, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11868 pattern childGuard
    simpa only [d1096, d2014, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1096, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11869 pattern childGuard
    simpa only [d1096, d2014, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11871 (pattern : Twelve) (guard : d1999 pattern = 1) : d1099 pattern ≤ (1 : Int) + d2015 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1099, d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11857 pattern childGuard
    simpa only [d1099, d2015, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1099, d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11870 pattern childGuard
    simpa only [d1099, d2015, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11872 (pattern : Twelve) (guard : d0 pattern = 1) : d438 pattern ≤ (1 : Int) + d1293 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11873 (pattern : Twelve) (guard : d1999 pattern = 1) : d1084 pattern ≤ (1 : Int) + d1293 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11872 pattern childGuard
    simpa only [d1999, d1084, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11852 pattern childGuard
    simpa only [d1999, d1084, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11874 (pattern : Twelve) (guard : d1999 pattern = 1) : d1092 pattern ≤ (1 : Int) + d2011 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1092, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11873 pattern childGuard
    simpa only [d1092, d2011, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1092, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11855 pattern childGuard
    simpa only [d1092, d2011, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11875 (pattern : Twelve) (guard : d0 pattern = 1) : d441 pattern ≤ (1 : Int) + d1297 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11876 (pattern : Twelve) (guard : d1999 pattern = 1) : d1085 pattern ≤ (1 : Int) + d1297 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11875 pattern childGuard
    simpa only [d1999, d1085, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11861 pattern childGuard
    simpa only [d1999, d1085, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11877 (pattern : Twelve) (guard : d1999 pattern = 1) : d1093 pattern ≤ (1 : Int) + d2012 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1093, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11876 pattern childGuard
    simpa only [d1093, d2012, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1093, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11867 pattern childGuard
    simpa only [d1093, d2012, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11878 (pattern : Twelve) (guard : d1999 pattern = 1) : d1097 pattern ≤ (1 : Int) + d2014 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1097, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11877 pattern childGuard
    simpa only [d1097, d2014, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1097, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11869 pattern childGuard
    simpa only [d1097, d2014, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11879 (pattern : Twelve) (guard : d1999 pattern = 1) : d1100 pattern ≤ (1 : Int) + d2015 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1100, d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11874 pattern childGuard
    simpa only [d1100, d2015, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1100, d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11878 pattern childGuard
    simpa only [d1100, d2015, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11880 (pattern : Twelve) (guard : d1999 pattern = 1) : d1102 pattern ≤ (1 : Int) + d2015 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11871 pattern childGuard
    simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11879 pattern childGuard
    simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11881 (pattern : Twelve) (guard : d1999 pattern = 1) : d1103 pattern ≤ (1 : Int) + d2015 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11880 pattern childGuard
    simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11879 pattern childGuard
    simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11882 (pattern : Twelve) (guard : d1 pattern = 1) : d879 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d879, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11186 pattern childGuard
    simpa only [d879, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11883 (pattern : Twelve) (guard : d1 pattern = 1) : d886 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11859 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11882 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11884 (pattern : Twelve) (guard : d1852 pattern = 1) : d1076 pattern ≤ (1 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1076, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11883 pattern childGuard
    simpa only [d1852, d1076, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1076, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11860 pattern childGuard
    simpa only [d1852, d1076, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11885 (pattern : Twelve) (guard : d1999 pattern = 1) : d1086 pattern ≤ (1 : Int) + d1297 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11875 pattern childGuard
    simpa only [d1999, d1086, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11884 pattern childGuard
    simpa only [d1999, d1086, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11886 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (1 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11195 pattern childGuard
    simpa only [d14, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11197 pattern childGuard
    simpa only [d14, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11887 (pattern : Twelve) (guard : d1 pattern = 1) : d118 pattern ≤ (1 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11195 pattern childGuard
    simpa only [d118, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11886 pattern childGuard
    simpa only [d118, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11888 (pattern : Twelve) (guard : d1 pattern = 1) : d881 pattern ≤ (1 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11132 pattern childGuard
    simpa only [d881, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11887 pattern childGuard
    simpa only [d881, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11889 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (1 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11186 pattern childGuard
    simpa only [d125, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d125, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11890 (pattern : Twelve) (guard : d1 pattern = 1) : d888 pattern ≤ (1 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11888 pattern childGuard
    simpa only [d888, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11889 pattern childGuard
    simpa only [d888, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11891 (pattern : Twelve) (guard : d1852 pattern = 1) : d1077 pattern ≤ (1 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1077, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11890 pattern childGuard
    simpa only [d1852, d1077, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1077, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11865 pattern childGuard
    simpa only [d1852, d1077, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11892 (pattern : Twelve) (guard : d1999 pattern = 1) : d1087 pattern ≤ (1 : Int) + d1299 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11863 pattern childGuard
    simpa only [d1999, d1087, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11891 pattern childGuard
    simpa only [d1999, d1087, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11893 (pattern : Twelve) (guard : d1999 pattern = 1) : d1094 pattern ≤ (1 : Int) + d2012 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1094, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11885 pattern childGuard
    simpa only [d1094, d2012, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1094, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11892 pattern childGuard
    simpa only [d1094, d2012, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11894 (pattern : Twelve) (guard : d1999 pattern = 1) : d1098 pattern ≤ (1 : Int) + d2014 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1098, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11893 pattern childGuard
    simpa only [d1098, d2014, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1098, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11869 pattern childGuard
    simpa only [d1098, d2014, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11895 (pattern : Twelve) (guard : d1999 pattern = 1) : d1101 pattern ≤ (1 : Int) + d2015 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1101, d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11874 pattern childGuard
    simpa only [d1101, d2015, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1101, d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11894 pattern childGuard
    simpa only [d1101, d2015, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11896 (pattern : Twelve) (guard : d1999 pattern = 1) : d1104 pattern ≤ (1 : Int) + d2015 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11881 pattern childGuard
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11895 pattern childGuard
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11897 (pattern : Twelve) (guard : d0 pattern = 1) : d1070 pattern ≤ (1 : Int) + d1649 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11898 (pattern : Twelve) (guard : d1852 pattern = 1) : d1294 pattern ≤ (1 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1294, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11067 pattern childGuard
    simpa only [d1852, d1294, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1294, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11335 pattern childGuard
    simpa only [d1852, d1294, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11899 (pattern : Twelve) (guard : d1999 pattern = 1) : d1472 pattern ≤ (1 : Int) + d1649 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11897 pattern childGuard
    simpa only [d1999, d1472, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11898 pattern childGuard
    simpa only [d1999, d1472, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
