/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons068
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c9660 (pattern : Twelve) (guard : d1871 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9572 pattern childGuard
    simpa only [d1871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9659 pattern childGuard
    simpa only [d1871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9661 (pattern : Twelve) (guard : d0 pattern = 1) : d1634 pattern ≤ (0 : Int) + d1353 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9662 (pattern : Twelve) (guard : d1871 pattern = 1) : d1635 pattern ≤ (0 : Int) + d1353 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9575 pattern childGuard
    simpa only [d1871, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9661 pattern childGuard
    simpa only [d1871, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9663 (pattern : Twelve) (guard : d1871 pattern = 1) : d1636 pattern ≤ (0 : Int) + d1354 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1636, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9660 pattern childGuard
    simpa only [d1636, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1636, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9662 pattern childGuard
    simpa only [d1636, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9664 (pattern : Twelve) (guard : d0 pattern = 1) : d1825 pattern ≤ (0 : Int) + d1677 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9665 (pattern : Twelve) (guard : d1871 pattern = 1) : d1826 pattern ≤ (0 : Int) + d1677 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9581 pattern childGuard
    simpa only [d1871, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9664 pattern childGuard
    simpa only [d1871, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9666 (pattern : Twelve) (guard : d1871 pattern = 1) : d1827 pattern ≤ (0 : Int) + d1678 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1827, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9600 pattern childGuard
    simpa only [d1827, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1827, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9665 pattern childGuard
    simpa only [d1827, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9667 (pattern : Twelve) (guard : d1876 pattern = 1) : d806 pattern ≤ (0 : Int) + d806 pattern := by
  omega
theorem c9668 (pattern : Twelve) (guard : d1876 pattern = 1) : d1267 pattern ≤ (0 : Int) + d1267 pattern := by
  omega
theorem c9669 (pattern : Twelve) (guard : d1876 pattern = 1) : d1636 pattern ≤ (0 : Int) + d1636 pattern := by
  omega
theorem c9670 (pattern : Twelve) (guard : d1876 pattern = 1) : d1827 pattern ≤ (0 : Int) + d1827 pattern := by
  omega
theorem c9671 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d114 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9672 (pattern : Twelve) (guard : d1871 pattern = 1) : d807 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9558 pattern childGuard
    simpa only [d1871, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9671 pattern childGuard
    simpa only [d1871, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9673 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d155 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9674 (pattern : Twelve) (guard : d1871 pattern = 1) : d808 pattern ≤ (0 : Int) + d155 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9561 pattern childGuard
    simpa only [d1871, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9673 pattern childGuard
    simpa only [d1871, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9675 (pattern : Twelve) (guard : d1871 pattern = 1) : d809 pattern ≤ (0 : Int) + d156 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d809, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9672 pattern childGuard
    simpa only [d809, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d809, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9674 pattern childGuard
    simpa only [d809, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9676 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d869 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9677 (pattern : Twelve) (guard : d1871 pattern = 1) : d1268 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9565 pattern childGuard
    simpa only [d1871, d1268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9676 pattern childGuard
    simpa only [d1871, d1268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9678 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d906 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9679 (pattern : Twelve) (guard : d1871 pattern = 1) : d1269 pattern ≤ (0 : Int) + d906 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9568 pattern childGuard
    simpa only [d1871, d1269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9678 pattern childGuard
    simpa only [d1871, d1269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9680 (pattern : Twelve) (guard : d1871 pattern = 1) : d1270 pattern ≤ (0 : Int) + d907 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1270, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9677 pattern childGuard
    simpa only [d1270, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1270, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9679 pattern childGuard
    simpa only [d1270, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9681 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1321 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9682 (pattern : Twelve) (guard : d1871 pattern = 1) : d1637 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9572 pattern childGuard
    simpa only [d1871, d1637, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9681 pattern childGuard
    simpa only [d1871, d1637, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9683 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1353 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9684 (pattern : Twelve) (guard : d1871 pattern = 1) : d1638 pattern ≤ (0 : Int) + d1353 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9575 pattern childGuard
    simpa only [d1871, d1638, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9683 pattern childGuard
    simpa only [d1871, d1638, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9685 (pattern : Twelve) (guard : d1871 pattern = 1) : d1639 pattern ≤ (0 : Int) + d1354 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1639, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9682 pattern childGuard
    simpa only [d1639, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1639, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9684 pattern childGuard
    simpa only [d1639, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9686 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1664 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9687 (pattern : Twelve) (guard : d1871 pattern = 1) : d1828 pattern ≤ (0 : Int) + d1664 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3 pattern childGuard
    simpa only [d1871, d1828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9686 pattern childGuard
    simpa only [d1871, d1828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9688 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1677 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9689 (pattern : Twelve) (guard : d1871 pattern = 1) : d1829 pattern ≤ (0 : Int) + d1677 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9581 pattern childGuard
    simpa only [d1871, d1829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9688 pattern childGuard
    simpa only [d1871, d1829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9690 (pattern : Twelve) (guard : d1871 pattern = 1) : d1830 pattern ≤ (0 : Int) + d1678 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1830, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9687 pattern childGuard
    simpa only [d1830, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1830, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9689 pattern childGuard
    simpa only [d1830, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9691 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d115 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9692 (pattern : Twelve) (guard : d1871 pattern = 1) : d807 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d807, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9558 pattern childGuard
    simpa only [d1871, d807, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d807, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9691 pattern childGuard
    simpa only [d1871, d807, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9693 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d804 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9694 (pattern : Twelve) (guard : d1871 pattern = 1) : d808 pattern ≤ (0 : Int) + d805 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d808, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9561 pattern childGuard
    simpa only [d1871, d808, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d808, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9693 pattern childGuard
    simpa only [d1871, d808, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9695 (pattern : Twelve) (guard : d1871 pattern = 1) : d809 pattern ≤ (0 : Int) + d806 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d809, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9692 pattern childGuard
    simpa only [d809, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d809, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9694 pattern childGuard
    simpa only [d809, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9696 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d870 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9697 (pattern : Twelve) (guard : d1871 pattern = 1) : d1268 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1268, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9565 pattern childGuard
    simpa only [d1871, d1268, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1268, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9696 pattern childGuard
    simpa only [d1871, d1268, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9698 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1265 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9699 (pattern : Twelve) (guard : d1871 pattern = 1) : d1269 pattern ≤ (0 : Int) + d1266 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1269, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9568 pattern childGuard
    simpa only [d1871, d1269, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1269, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9698 pattern childGuard
    simpa only [d1871, d1269, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9700 (pattern : Twelve) (guard : d1871 pattern = 1) : d1270 pattern ≤ (0 : Int) + d1267 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1270, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9697 pattern childGuard
    simpa only [d1270, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1270, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9699 pattern childGuard
    simpa only [d1270, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9701 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1322 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9702 (pattern : Twelve) (guard : d1871 pattern = 1) : d1637 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1637, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9572 pattern childGuard
    simpa only [d1871, d1637, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1637, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9701 pattern childGuard
    simpa only [d1871, d1637, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9703 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1634 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9704 (pattern : Twelve) (guard : d1871 pattern = 1) : d1638 pattern ≤ (0 : Int) + d1635 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1638, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9575 pattern childGuard
    simpa only [d1871, d1638, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1638, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9703 pattern childGuard
    simpa only [d1871, d1638, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9705 (pattern : Twelve) (guard : d1871 pattern = 1) : d1639 pattern ≤ (0 : Int) + d1636 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1639, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9702 pattern childGuard
    simpa only [d1639, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1639, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9704 pattern childGuard
    simpa only [d1639, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9706 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1825 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9707 (pattern : Twelve) (guard : d1871 pattern = 1) : d1829 pattern ≤ (0 : Int) + d1826 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1829, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9581 pattern childGuard
    simpa only [d1871, d1829, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1829, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9706 pattern childGuard
    simpa only [d1871, d1829, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9708 (pattern : Twelve) (guard : d1871 pattern = 1) : d1830 pattern ≤ (0 : Int) + d1827 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1830, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9687 pattern childGuard
    simpa only [d1830, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1830, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9707 pattern childGuard
    simpa only [d1830, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9709 (pattern : Twelve) (guard : d0 pattern = 1) : d807 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9710 (pattern : Twelve) (guard : d1877 pattern = 1) : d807 pattern ≤ (0 : Int) + d810 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1877, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9692 pattern childGuard
    simpa only [d1877, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1877, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9709 pattern childGuard
    simpa only [d1877, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9711 (pattern : Twelve) (guard : d0 pattern = 1) : d808 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9712 (pattern : Twelve) (guard : d1877 pattern = 1) : d808 pattern ≤ (0 : Int) + d811 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1877, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9694 pattern childGuard
    simpa only [d1877, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1877, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9711 pattern childGuard
    simpa only [d1877, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9713 (pattern : Twelve) (guard : d1877 pattern = 1) : d809 pattern ≤ (0 : Int) + d812 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1877 pattern = 1 := by simpa only [d809, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9710 pattern childGuard
    simpa only [d809, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1877 pattern = 1 := by simpa only [d809, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9712 pattern childGuard
    simpa only [d809, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9714 (pattern : Twelve) (guard : d0 pattern = 1) : d1268 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9715 (pattern : Twelve) (guard : d1877 pattern = 1) : d1268 pattern ≤ (0 : Int) + d1271 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1877, d1271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9697 pattern childGuard
    simpa only [d1877, d1271, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1877, d1271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9714 pattern childGuard
    simpa only [d1877, d1271, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9716 (pattern : Twelve) (guard : d0 pattern = 1) : d1269 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9717 (pattern : Twelve) (guard : d1877 pattern = 1) : d1269 pattern ≤ (0 : Int) + d1272 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1877, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9699 pattern childGuard
    simpa only [d1877, d1272, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1877, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9716 pattern childGuard
    simpa only [d1877, d1272, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9718 (pattern : Twelve) (guard : d1877 pattern = 1) : d1270 pattern ≤ (0 : Int) + d1273 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1877 pattern = 1 := by simpa only [d1270, d1273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9715 pattern childGuard
    simpa only [d1270, d1273, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1877 pattern = 1 := by simpa only [d1270, d1273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9717 pattern childGuard
    simpa only [d1270, d1273, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9719 (pattern : Twelve) (guard : d0 pattern = 1) : d1637 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9720 (pattern : Twelve) (guard : d1877 pattern = 1) : d1637 pattern ≤ (0 : Int) + d1640 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1877, d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9702 pattern childGuard
    simpa only [d1877, d1640, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1877, d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9719 pattern childGuard
    simpa only [d1877, d1640, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9721 (pattern : Twelve) (guard : d0 pattern = 1) : d1638 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9722 (pattern : Twelve) (guard : d1877 pattern = 1) : d1638 pattern ≤ (0 : Int) + d1641 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1877, d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9704 pattern childGuard
    simpa only [d1877, d1641, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1877, d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9721 pattern childGuard
    simpa only [d1877, d1641, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9723 (pattern : Twelve) (guard : d1877 pattern = 1) : d1639 pattern ≤ (0 : Int) + d1642 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1877 pattern = 1 := by simpa only [d1639, d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9720 pattern childGuard
    simpa only [d1639, d1642, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1877 pattern = 1 := by simpa only [d1639, d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9722 pattern childGuard
    simpa only [d1639, d1642, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9724 (pattern : Twelve) (guard : d0 pattern = 1) : d1828 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9725 (pattern : Twelve) (guard : d1877 pattern = 1) : d1828 pattern ≤ (0 : Int) + d1831 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1877, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9687 pattern childGuard
    simpa only [d1877, d1831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1877, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9724 pattern childGuard
    simpa only [d1877, d1831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9726 (pattern : Twelve) (guard : d0 pattern = 1) : d1829 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9727 (pattern : Twelve) (guard : d1877 pattern = 1) : d1829 pattern ≤ (0 : Int) + d1832 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1877, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9707 pattern childGuard
    simpa only [d1877, d1832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1877, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9726 pattern childGuard
    simpa only [d1877, d1832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9728 (pattern : Twelve) (guard : d1877 pattern = 1) : d1830 pattern ≤ (0 : Int) + d1833 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1877 pattern = 1 := by simpa only [d1830, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9725 pattern childGuard
    simpa only [d1830, d1833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1877 pattern = 1 := by simpa only [d1830, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9727 pattern childGuard
    simpa only [d1830, d1833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9729 (pattern : Twelve) (guard : d0 pattern = 1) : d156 pattern ≤ (0 : Int) + d156 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9730 (pattern : Twelve) (guard : d0 pattern = 1) : d907 pattern ≤ (0 : Int) + d907 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9731 (pattern : Twelve) (guard : d0 pattern = 1) : d1354 pattern ≤ (0 : Int) + d1354 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9732 (pattern : Twelve) (guard : d0 pattern = 1) : d1678 pattern ≤ (0 : Int) + d1678 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9733 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d116 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9734 (pattern : Twelve) (guard : d1873 pattern = 1) : d810 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1873, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c0 pattern childGuard
    simpa only [d1873, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1873, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9733 pattern childGuard
    simpa only [d1873, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9735 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d805 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9736 (pattern : Twelve) (guard : d1873 pattern = 1) : d811 pattern ≤ (0 : Int) + d805 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1873, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9628 pattern childGuard
    simpa only [d1873, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1873, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9735 pattern childGuard
    simpa only [d1873, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9737 (pattern : Twelve) (guard : d1873 pattern = 1) : d812 pattern ≤ (0 : Int) + d806 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1873 pattern = 1 := by simpa only [d812, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9734 pattern childGuard
    simpa only [d812, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1873 pattern = 1 := by simpa only [d812, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9736 pattern childGuard
    simpa only [d812, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9738 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d871 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9739 (pattern : Twelve) (guard : d1873 pattern = 1) : d1271 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1873, d1271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1 pattern childGuard
    simpa only [d1873, d1271, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1873, d1271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9738 pattern childGuard
    simpa only [d1873, d1271, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9740 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1266 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9741 (pattern : Twelve) (guard : d1873 pattern = 1) : d1272 pattern ≤ (0 : Int) + d1266 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1873, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9634 pattern childGuard
    simpa only [d1873, d1272, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1873, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9740 pattern childGuard
    simpa only [d1873, d1272, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9742 (pattern : Twelve) (guard : d1873 pattern = 1) : d1273 pattern ≤ (0 : Int) + d1267 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1873 pattern = 1 := by simpa only [d1273, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9739 pattern childGuard
    simpa only [d1273, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1873 pattern = 1 := by simpa only [d1273, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9741 pattern childGuard
    simpa only [d1273, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9743 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1323 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9744 (pattern : Twelve) (guard : d1873 pattern = 1) : d1640 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1873, d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2 pattern childGuard
    simpa only [d1873, d1640, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1873, d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9743 pattern childGuard
    simpa only [d1873, d1640, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9745 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1635 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9746 (pattern : Twelve) (guard : d1873 pattern = 1) : d1641 pattern ≤ (0 : Int) + d1635 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1873, d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9640 pattern childGuard
    simpa only [d1873, d1641, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1873, d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9745 pattern childGuard
    simpa only [d1873, d1641, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9747 (pattern : Twelve) (guard : d1873 pattern = 1) : d1642 pattern ≤ (0 : Int) + d1636 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1873 pattern = 1 := by simpa only [d1642, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9744 pattern childGuard
    simpa only [d1642, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1873 pattern = 1 := by simpa only [d1642, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9746 pattern childGuard
    simpa only [d1642, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9748 (pattern : Twelve) (guard : d1873 pattern = 1) : d1831 pattern ≤ (0 : Int) + d1664 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1873, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3 pattern childGuard
    simpa only [d1873, d1831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1873, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9686 pattern childGuard
    simpa only [d1873, d1831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9749 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1826 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9750 (pattern : Twelve) (guard : d1873 pattern = 1) : d1832 pattern ≤ (0 : Int) + d1826 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1873, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9645 pattern childGuard
    simpa only [d1873, d1832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1873, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9749 pattern childGuard
    simpa only [d1873, d1832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9751 (pattern : Twelve) (guard : d1873 pattern = 1) : d1833 pattern ≤ (0 : Int) + d1827 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1873 pattern = 1 := by simpa only [d1833, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9748 pattern childGuard
    simpa only [d1833, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1873 pattern = 1 := by simpa only [d1833, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9750 pattern childGuard
    simpa only [d1833, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9752 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d807 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9753 (pattern : Twelve) (guard : d1877 pattern = 1) : d810 pattern ≤ (0 : Int) + d807 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1877, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9609 pattern childGuard
    simpa only [d1877, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1877, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9752 pattern childGuard
    simpa only [d1877, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9754 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d808 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9755 (pattern : Twelve) (guard : d1877 pattern = 1) : d811 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1877, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9611 pattern childGuard
    simpa only [d1877, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1877, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9754 pattern childGuard
    simpa only [d1877, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9756 (pattern : Twelve) (guard : d1877 pattern = 1) : d812 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1877 pattern = 1 := by simpa only [d812, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9753 pattern childGuard
    simpa only [d812, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1877 pattern = 1 := by simpa only [d812, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9755 pattern childGuard
    simpa only [d812, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9757 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1268 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9758 (pattern : Twelve) (guard : d1877 pattern = 1) : d1271 pattern ≤ (0 : Int) + d1268 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1877, d1271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9614 pattern childGuard
    simpa only [d1877, d1271, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1877, d1271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9757 pattern childGuard
    simpa only [d1877, d1271, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9759 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1269 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9760 (pattern : Twelve) (guard : d1877 pattern = 1) : d1272 pattern ≤ (0 : Int) + d1269 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1877, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9616 pattern childGuard
    simpa only [d1877, d1272, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1877, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9759 pattern childGuard
    simpa only [d1877, d1272, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9761 (pattern : Twelve) (guard : d1877 pattern = 1) : d1273 pattern ≤ (0 : Int) + d1270 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1877 pattern = 1 := by simpa only [d1273, d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9758 pattern childGuard
    simpa only [d1273, d1270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1877 pattern = 1 := by simpa only [d1273, d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9760 pattern childGuard
    simpa only [d1273, d1270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9762 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1637 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9763 (pattern : Twelve) (guard : d1877 pattern = 1) : d1640 pattern ≤ (0 : Int) + d1637 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1877, d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9619 pattern childGuard
    simpa only [d1877, d1640, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1877, d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9762 pattern childGuard
    simpa only [d1877, d1640, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9764 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1638 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9765 (pattern : Twelve) (guard : d1877 pattern = 1) : d1641 pattern ≤ (0 : Int) + d1638 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1877, d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9621 pattern childGuard
    simpa only [d1877, d1641, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1877, d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9764 pattern childGuard
    simpa only [d1877, d1641, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9766 (pattern : Twelve) (guard : d1877 pattern = 1) : d1642 pattern ≤ (0 : Int) + d1639 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1877 pattern = 1 := by simpa only [d1642, d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9763 pattern childGuard
    simpa only [d1642, d1639, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1877 pattern = 1 := by simpa only [d1642, d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9765 pattern childGuard
    simpa only [d1642, d1639, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9767 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1828 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9768 (pattern : Twelve) (guard : d1877 pattern = 1) : d1831 pattern ≤ (0 : Int) + d1828 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1877, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9580 pattern childGuard
    simpa only [d1877, d1831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1877, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9767 pattern childGuard
    simpa only [d1877, d1831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9769 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1829 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9770 (pattern : Twelve) (guard : d1877 pattern = 1) : d1832 pattern ≤ (0 : Int) + d1829 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1877, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9624 pattern childGuard
    simpa only [d1877, d1832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1877, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9769 pattern childGuard
    simpa only [d1877, d1832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9771 (pattern : Twelve) (guard : d1877 pattern = 1) : d1833 pattern ≤ (0 : Int) + d1830 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1877 pattern = 1 := by simpa only [d1833, d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9768 pattern childGuard
    simpa only [d1833, d1830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1877 pattern = 1 := by simpa only [d1833, d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9770 pattern childGuard
    simpa only [d1833, d1830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9772 (pattern : Twelve) (guard : d1 pattern = 1) : d806 pattern ≤ (0 : Int) + d806 pattern := by
  omega
theorem c9773 (pattern : Twelve) (guard : d1 pattern = 1) : d1267 pattern ≤ (0 : Int) + d1267 pattern := by
  omega
theorem c9774 (pattern : Twelve) (guard : d1 pattern = 1) : d1636 pattern ≤ (0 : Int) + d1636 pattern := by
  omega
theorem c9775 (pattern : Twelve) (guard : d1 pattern = 1) : d1827 pattern ≤ (0 : Int) + d1827 pattern := by
  omega
theorem c9776 (pattern : Twelve) (guard : d1878 pattern = 1) : d116 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c0 pattern childGuard
    simpa only [d1878, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9626 pattern childGuard
    simpa only [d1878, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9777 (pattern : Twelve) (guard : d1878 pattern = 1) : d871 pattern ≤ (0 : Int) + d1274 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1 pattern childGuard
    simpa only [d1878, d1274, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9632 pattern childGuard
    simpa only [d1878, d1274, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9778 (pattern : Twelve) (guard : d1878 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1643 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2 pattern childGuard
    simpa only [d1878, d1643, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9638 pattern childGuard
    simpa only [d1878, d1643, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9779 (pattern : Twelve) (guard : d1878 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1834 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3 pattern childGuard
    simpa only [d1878, d1834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9579 pattern childGuard
    simpa only [d1878, d1834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9780 (pattern : Twelve) (guard : d0 pattern = 1) : d116 pattern ≤ (0 : Int) + d805 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9781 (pattern : Twelve) (guard : d1878 pattern = 1) : d116 pattern ≤ (0 : Int) + d806 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c0 pattern childGuard
    simpa only [d1878, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9780 pattern childGuard
    simpa only [d1878, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9782 (pattern : Twelve) (guard : d0 pattern = 1) : d871 pattern ≤ (0 : Int) + d1266 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9783 (pattern : Twelve) (guard : d1878 pattern = 1) : d871 pattern ≤ (0 : Int) + d1267 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1 pattern childGuard
    simpa only [d1878, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9782 pattern childGuard
    simpa only [d1878, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9784 (pattern : Twelve) (guard : d0 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1635 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9785 (pattern : Twelve) (guard : d1878 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1636 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2 pattern childGuard
    simpa only [d1878, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9784 pattern childGuard
    simpa only [d1878, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9786 (pattern : Twelve) (guard : d0 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1826 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9787 (pattern : Twelve) (guard : d1878 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1827 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3 pattern childGuard
    simpa only [d1878, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9786 pattern childGuard
    simpa only [d1878, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9788 (pattern : Twelve) (guard : d1878 pattern = 1) : d813 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c0 pattern childGuard
    simpa only [d1878, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9733 pattern childGuard
    simpa only [d1878, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9789 (pattern : Twelve) (guard : d1878 pattern = 1) : d1274 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1 pattern childGuard
    simpa only [d1878, d1274, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9738 pattern childGuard
    simpa only [d1878, d1274, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9790 (pattern : Twelve) (guard : d1878 pattern = 1) : d1643 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2 pattern childGuard
    simpa only [d1878, d1643, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9743 pattern childGuard
    simpa only [d1878, d1643, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9791 (pattern : Twelve) (guard : d1878 pattern = 1) : d1834 pattern ≤ (0 : Int) + d1664 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3 pattern childGuard
    simpa only [d1878, d1834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9686 pattern childGuard
    simpa only [d1878, d1834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9792 (pattern : Twelve) (guard : d1878 pattern = 1) : d813 pattern ≤ (0 : Int) + d806 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d813, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c0 pattern childGuard
    simpa only [d1878, d813, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d813, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9735 pattern childGuard
    simpa only [d1878, d813, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9793 (pattern : Twelve) (guard : d1878 pattern = 1) : d1274 pattern ≤ (0 : Int) + d1267 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1274, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1 pattern childGuard
    simpa only [d1878, d1274, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1274, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9740 pattern childGuard
    simpa only [d1878, d1274, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9794 (pattern : Twelve) (guard : d1878 pattern = 1) : d1643 pattern ≤ (0 : Int) + d1636 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1643, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2 pattern childGuard
    simpa only [d1878, d1643, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1643, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9745 pattern childGuard
    simpa only [d1878, d1643, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9795 (pattern : Twelve) (guard : d1878 pattern = 1) : d1834 pattern ≤ (0 : Int) + d1827 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1834, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3 pattern childGuard
    simpa only [d1878, d1834, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1834, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9749 pattern childGuard
    simpa only [d1878, d1834, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9796 (pattern : Twelve) (guard : d1878 pattern = 1) : d806 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d806, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c0 pattern childGuard
    simpa only [d1878, d806, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d806, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9629 pattern childGuard
    simpa only [d1878, d806, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9797 (pattern : Twelve) (guard : d1878 pattern = 1) : d1267 pattern ≤ (0 : Int) + d1274 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1267, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1 pattern childGuard
    simpa only [d1878, d1267, d1274, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1267, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9635 pattern childGuard
    simpa only [d1878, d1267, d1274, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9798 (pattern : Twelve) (guard : d1878 pattern = 1) : d1636 pattern ≤ (0 : Int) + d1643 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1636, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2 pattern childGuard
    simpa only [d1878, d1636, d1643, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1636, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9641 pattern childGuard
    simpa only [d1878, d1636, d1643, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9799 (pattern : Twelve) (guard : d1878 pattern = 1) : d1827 pattern ≤ (0 : Int) + d1834 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1827, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3 pattern childGuard
    simpa only [d1878, d1827, d1834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1827, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9646 pattern childGuard
    simpa only [d1878, d1827, d1834, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
