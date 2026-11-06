/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons057
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c8120 (pattern : Twelve) (guard : d1866 pattern = 1) : d1812 pattern ≤ (0 : Int) + d1677 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1812, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8110 pattern childGuard
    simpa only [d1812, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1812, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8119 pattern childGuard
    simpa only [d1812, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8121 (pattern : Twelve) (guard : d1866 pattern = 1) : d1813 pattern ≤ (0 : Int) + d1678 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1813, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8107 pattern childGuard
    simpa only [d1813, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1813, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8120 pattern childGuard
    simpa only [d1813, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8122 (pattern : Twelve) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8123 (pattern : Twelve) (guard : d1867 pattern = 1) : d7 pattern ≤ (0 : Int) + d477 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7730 pattern childGuard
    simpa only [d1867, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8122 pattern childGuard
    simpa only [d1867, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8124 (pattern : Twelve) (guard : d1867 pattern = 1) : d646 pattern ≤ (0 : Int) + d498 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d646, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3245 pattern childGuard
    simpa only [d646, d498, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d646, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8123 pattern childGuard
    simpa only [d646, d498, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8125 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (0 : Int) + d157 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8126 (pattern : Twelve) (guard : d1867 pattern = 1) : d634 pattern ≤ (0 : Int) + d478 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d634, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7730 pattern childGuard
    simpa only [d1867, d634, d478, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d634, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8125 pattern childGuard
    simpa only [d1867, d634, d478, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8127 (pattern : Twelve) (guard : d1867 pattern = 1) : d647 pattern ≤ (0 : Int) + d499 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d647, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3245 pattern childGuard
    simpa only [d647, d499, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d647, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8126 pattern childGuard
    simpa only [d647, d499, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8128 (pattern : Twelve) (guard : d1867 pattern = 1) : d680 pattern ≤ (0 : Int) + d532 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d680, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8124 pattern childGuard
    simpa only [d680, d532, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d680, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8127 pattern childGuard
    simpa only [d680, d532, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8129 (pattern : Twelve) (guard : d0 pattern = 1) : d157 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8130 (pattern : Twelve) (guard : d1867 pattern = 1) : d157 pattern ≤ (0 : Int) + d479 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7736 pattern childGuard
    simpa only [d1867, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8129 pattern childGuard
    simpa only [d1867, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8131 (pattern : Twelve) (guard : d1867 pattern = 1) : d648 pattern ≤ (0 : Int) + d500 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d648, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7387 pattern childGuard
    simpa only [d648, d500, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d648, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8130 pattern childGuard
    simpa only [d648, d500, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8132 (pattern : Twelve) (guard : d1867 pattern = 1) : d681 pattern ≤ (0 : Int) + d533 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d681, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7386 pattern childGuard
    simpa only [d681, d533, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d681, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8131 pattern childGuard
    simpa only [d681, d533, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8133 (pattern : Twelve) (guard : d1867 pattern = 1) : d709 pattern ≤ (0 : Int) + d561 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d709, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8128 pattern childGuard
    simpa only [d709, d561, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d709, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8132 pattern childGuard
    simpa only [d709, d561, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8134 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8135 (pattern : Twelve) (guard : d1867 pattern = 1) : d158 pattern ≤ (0 : Int) + d480 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8134 pattern childGuard
    simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8136 (pattern : Twelve) (guard : d1867 pattern = 1) : d649 pattern ≤ (0 : Int) + d501 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d649, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7387 pattern childGuard
    simpa only [d649, d501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d649, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d649, d501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8137 (pattern : Twelve) (guard : d1867 pattern = 1) : d682 pattern ≤ (0 : Int) + d534 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d682, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8127 pattern childGuard
    simpa only [d682, d534, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d682, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8136 pattern childGuard
    simpa only [d682, d534, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8138 (pattern : Twelve) (guard : d0 pattern = 1) : d160 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8139 (pattern : Twelve) (guard : d1867 pattern = 1) : d635 pattern ≤ (0 : Int) + d481 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d635, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7747 pattern childGuard
    simpa only [d1867, d635, d481, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d635, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8138 pattern childGuard
    simpa only [d1867, d635, d481, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8140 (pattern : Twelve) (guard : d1867 pattern = 1) : d650 pattern ≤ (0 : Int) + d502 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d650, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7387 pattern childGuard
    simpa only [d650, d502, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d650, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8139 pattern childGuard
    simpa only [d650, d502, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8141 (pattern : Twelve) (guard : d1867 pattern = 1) : d636 pattern ≤ (0 : Int) + d482 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d636, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7751 pattern childGuard
    simpa only [d1867, d636, d482, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d636, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8129 pattern childGuard
    simpa only [d1867, d636, d482, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8142 (pattern : Twelve) (guard : d1867 pattern = 1) : d651 pattern ≤ (0 : Int) + d503 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d651, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8141 pattern childGuard
    simpa only [d651, d503, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d651, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d651, d503, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8143 (pattern : Twelve) (guard : d1867 pattern = 1) : d683 pattern ≤ (0 : Int) + d535 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d683, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8140 pattern childGuard
    simpa only [d683, d535, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d683, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8142 pattern childGuard
    simpa only [d683, d535, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8144 (pattern : Twelve) (guard : d1867 pattern = 1) : d710 pattern ≤ (0 : Int) + d562 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d710, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8137 pattern childGuard
    simpa only [d710, d562, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d710, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8143 pattern childGuard
    simpa only [d710, d562, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8145 (pattern : Twelve) (guard : d1867 pattern = 1) : d736 pattern ≤ (0 : Int) + d588 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d736, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8133 pattern childGuard
    simpa only [d736, d588, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d736, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8144 pattern childGuard
    simpa only [d736, d588, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8146 (pattern : Twelve) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8147 (pattern : Twelve) (guard : d1867 pattern = 1) : d10 pattern ≤ (0 : Int) + d483 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7758 pattern childGuard
    simpa only [d1867, d483, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8146 pattern childGuard
    simpa only [d1867, d483, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8148 (pattern : Twelve) (guard : d0 pattern = 1) : d160 pattern ≤ (0 : Int) + d159 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8149 (pattern : Twelve) (guard : d1867 pattern = 1) : d637 pattern ≤ (0 : Int) + d484 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d637, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7760 pattern childGuard
    simpa only [d1867, d637, d484, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d637, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8148 pattern childGuard
    simpa only [d1867, d637, d484, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8150 (pattern : Twelve) (guard : d1867 pattern = 1) : d652 pattern ≤ (0 : Int) + d504 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d652, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8147 pattern childGuard
    simpa only [d652, d504, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d652, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8149 pattern childGuard
    simpa only [d652, d504, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8151 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (0 : Int) + d160 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8152 (pattern : Twelve) (guard : d1867 pattern = 1) : d638 pattern ≤ (0 : Int) + d485 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d638, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7758 pattern childGuard
    simpa only [d1867, d638, d485, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d638, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8151 pattern childGuard
    simpa only [d1867, d638, d485, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8153 (pattern : Twelve) (guard : d1867 pattern = 1) : d639 pattern ≤ (0 : Int) + d486 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d639, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7765 pattern childGuard
    simpa only [d1867, d639, d486, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d639, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2866 pattern childGuard
    simpa only [d1867, d639, d486, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8154 (pattern : Twelve) (guard : d1867 pattern = 1) : d653 pattern ≤ (0 : Int) + d505 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d653, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8152 pattern childGuard
    simpa only [d653, d505, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d653, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8153 pattern childGuard
    simpa only [d653, d505, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8155 (pattern : Twelve) (guard : d1867 pattern = 1) : d684 pattern ≤ (0 : Int) + d536 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d684, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8150 pattern childGuard
    simpa only [d684, d536, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d684, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8154 pattern childGuard
    simpa only [d684, d536, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8156 (pattern : Twelve) (guard : d1867 pattern = 1) : d160 pattern ≤ (0 : Int) + d487 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8138 pattern childGuard
    simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8157 (pattern : Twelve) (guard : d1867 pattern = 1) : d654 pattern ≤ (0 : Int) + d506 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d654, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8152 pattern childGuard
    simpa only [d654, d506, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d654, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8156 pattern childGuard
    simpa only [d654, d506, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8158 (pattern : Twelve) (guard : d1867 pattern = 1) : d21 pattern ≤ (0 : Int) + d170 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d21, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3696 pattern childGuard
    simpa only [d1867, d21, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d21, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2875 pattern childGuard
    simpa only [d1867, d21, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8159 (pattern : Twelve) (guard : d1867 pattern = 1) : d655 pattern ≤ (0 : Int) + d507 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d655, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d655, d507, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d655, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8158 pattern childGuard
    simpa only [d655, d507, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8160 (pattern : Twelve) (guard : d1867 pattern = 1) : d685 pattern ≤ (0 : Int) + d537 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d685, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8157 pattern childGuard
    simpa only [d685, d537, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d685, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8159 pattern childGuard
    simpa only [d685, d537, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8161 (pattern : Twelve) (guard : d1867 pattern = 1) : d711 pattern ≤ (0 : Int) + d563 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d711, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8155 pattern childGuard
    simpa only [d711, d563, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d711, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8160 pattern childGuard
    simpa only [d711, d563, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8162 (pattern : Twelve) (guard : d1867 pattern = 1) : d656 pattern ≤ (0 : Int) + d508 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d656, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d656, d508, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d656, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d656, d508, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8163 (pattern : Twelve) (guard : d1867 pattern = 1) : d686 pattern ≤ (0 : Int) + d538 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d686, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8157 pattern childGuard
    simpa only [d686, d538, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d686, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8162 pattern childGuard
    simpa only [d686, d538, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8164 (pattern : Twelve) (guard : d1867 pattern = 1) : d657 pattern ≤ (0 : Int) + d509 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d657, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d657, d509, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d657, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8156 pattern childGuard
    simpa only [d657, d509, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8165 (pattern : Twelve) (guard : d1867 pattern = 1) : d687 pattern ≤ (0 : Int) + d539 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d687, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d687, d539, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d687, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8142 pattern childGuard
    simpa only [d687, d539, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8166 (pattern : Twelve) (guard : d1867 pattern = 1) : d712 pattern ≤ (0 : Int) + d564 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d712, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8163 pattern childGuard
    simpa only [d712, d564, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d712, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8165 pattern childGuard
    simpa only [d712, d564, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8167 (pattern : Twelve) (guard : d1867 pattern = 1) : d737 pattern ≤ (0 : Int) + d589 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d737, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8161 pattern childGuard
    simpa only [d737, d589, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d737, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8166 pattern childGuard
    simpa only [d737, d589, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8168 (pattern : Twelve) (guard : d1867 pattern = 1) : d754 pattern ≤ (0 : Int) + d606 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d754, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8145 pattern childGuard
    simpa only [d754, d606, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d754, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8167 pattern childGuard
    simpa only [d754, d606, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8169 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (0 : Int) + d159 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8170 (pattern : Twelve) (guard : d1867 pattern = 1) : d640 pattern ≤ (0 : Int) + d488 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d640, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7782 pattern childGuard
    simpa only [d1867, d640, d488, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d640, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8169 pattern childGuard
    simpa only [d1867, d640, d488, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8171 (pattern : Twelve) (guard : d1867 pattern = 1) : d658 pattern ≤ (0 : Int) + d510 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d658, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8147 pattern childGuard
    simpa only [d658, d510, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d658, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8170 pattern childGuard
    simpa only [d658, d510, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8172 (pattern : Twelve) (guard : d1867 pattern = 1) : d659 pattern ≤ (0 : Int) + d511 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d659, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8152 pattern childGuard
    simpa only [d659, d511, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d659, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d659, d511, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8173 (pattern : Twelve) (guard : d1867 pattern = 1) : d688 pattern ≤ (0 : Int) + d540 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d688, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8171 pattern childGuard
    simpa only [d688, d540, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d688, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8172 pattern childGuard
    simpa only [d688, d540, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8174 (pattern : Twelve) (guard : d1867 pattern = 1) : d660 pattern ≤ (0 : Int) + d512 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d660, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8152 pattern childGuard
    simpa only [d660, d512, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d660, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8130 pattern childGuard
    simpa only [d660, d512, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8175 (pattern : Twelve) (guard : d1867 pattern = 1) : d661 pattern ≤ (0 : Int) + d513 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d661, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d661, d513, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d661, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8130 pattern childGuard
    simpa only [d661, d513, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8176 (pattern : Twelve) (guard : d1867 pattern = 1) : d689 pattern ≤ (0 : Int) + d541 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d689, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8174 pattern childGuard
    simpa only [d689, d541, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d689, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8175 pattern childGuard
    simpa only [d689, d541, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8177 (pattern : Twelve) (guard : d1867 pattern = 1) : d713 pattern ≤ (0 : Int) + d565 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d713, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8173 pattern childGuard
    simpa only [d713, d565, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d713, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8176 pattern childGuard
    simpa only [d713, d565, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8178 (pattern : Twelve) (guard : d1867 pattern = 1) : d690 pattern ≤ (0 : Int) + d542 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d690, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8172 pattern childGuard
    simpa only [d690, d542, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d690, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d690, d542, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8179 (pattern : Twelve) (guard : d1867 pattern = 1) : d714 pattern ≤ (0 : Int) + d566 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d714, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8178 pattern childGuard
    simpa only [d714, d566, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d714, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8165 pattern childGuard
    simpa only [d714, d566, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8180 (pattern : Twelve) (guard : d1867 pattern = 1) : d738 pattern ≤ (0 : Int) + d590 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d738, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8177 pattern childGuard
    simpa only [d738, d590, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d738, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8179 pattern childGuard
    simpa only [d738, d590, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8181 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (0 : Int) + d13 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8182 (pattern : Twelve) (guard : d1867 pattern = 1) : d641 pattern ≤ (0 : Int) + d489 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d641, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7795 pattern childGuard
    simpa only [d1867, d641, d489, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d641, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8181 pattern childGuard
    simpa only [d1867, d641, d489, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8183 (pattern : Twelve) (guard : d1867 pattern = 1) : d662 pattern ≤ (0 : Int) + d514 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d662, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8182 pattern childGuard
    simpa only [d662, d514, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d662, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8156 pattern childGuard
    simpa only [d662, d514, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8184 (pattern : Twelve) (guard : d1867 pattern = 1) : d663 pattern ≤ (0 : Int) + d515 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d663, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d663, d515, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d663, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d663, d515, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8185 (pattern : Twelve) (guard : d1867 pattern = 1) : d691 pattern ≤ (0 : Int) + d543 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d691, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8183 pattern childGuard
    simpa only [d691, d543, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d691, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8184 pattern childGuard
    simpa only [d691, d543, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8186 (pattern : Twelve) (guard : d1867 pattern = 1) : d692 pattern ≤ (0 : Int) + d544 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d692, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d692, d544, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d692, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8184 pattern childGuard
    simpa only [d692, d544, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8187 (pattern : Twelve) (guard : d1867 pattern = 1) : d715 pattern ≤ (0 : Int) + d567 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d715, d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8185 pattern childGuard
    simpa only [d715, d567, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d715, d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8186 pattern childGuard
    simpa only [d715, d567, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8188 (pattern : Twelve) (guard : d1867 pattern = 1) : d716 pattern ≤ (0 : Int) + d568 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d716, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8186 pattern childGuard
    simpa only [d716, d568, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d716, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8165 pattern childGuard
    simpa only [d716, d568, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8189 (pattern : Twelve) (guard : d1867 pattern = 1) : d739 pattern ≤ (0 : Int) + d591 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d739, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8187 pattern childGuard
    simpa only [d739, d591, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d739, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8188 pattern childGuard
    simpa only [d739, d591, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8190 (pattern : Twelve) (guard : d1867 pattern = 1) : d755 pattern ≤ (0 : Int) + d607 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d755, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8180 pattern childGuard
    simpa only [d755, d607, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d755, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8189 pattern childGuard
    simpa only [d755, d607, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8191 (pattern : Twelve) (guard : d1867 pattern = 1) : d766 pattern ≤ (0 : Int) + d618 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d766, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8168 pattern childGuard
    simpa only [d766, d618, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d766, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8190 pattern childGuard
    simpa only [d766, d618, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8192 (pattern : Twelve) (guard : d0 pattern = 1) : d630 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8193 (pattern : Twelve) (guard : d1867 pattern = 1) : d630 pattern ≤ (0 : Int) + d490 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7782 pattern childGuard
    simpa only [d1867, d490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8192 pattern childGuard
    simpa only [d1867, d490, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8194 (pattern : Twelve) (guard : d0 pattern = 1) : d160 pattern ≤ (0 : Int) + d13 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8195 (pattern : Twelve) (guard : d1867 pattern = 1) : d642 pattern ≤ (0 : Int) + d491 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d642, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7810 pattern childGuard
    simpa only [d1867, d642, d491, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d642, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8194 pattern childGuard
    simpa only [d1867, d642, d491, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8196 (pattern : Twelve) (guard : d1867 pattern = 1) : d664 pattern ≤ (0 : Int) + d516 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d664, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8193 pattern childGuard
    simpa only [d664, d516, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d664, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8195 pattern childGuard
    simpa only [d664, d516, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8197 (pattern : Twelve) (guard : d1867 pattern = 1) : d665 pattern ≤ (0 : Int) + d517 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d665, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8170 pattern childGuard
    simpa only [d665, d517, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d665, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8156 pattern childGuard
    simpa only [d665, d517, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8198 (pattern : Twelve) (guard : d1867 pattern = 1) : d693 pattern ≤ (0 : Int) + d545 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d693, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8196 pattern childGuard
    simpa only [d693, d545, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d693, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8197 pattern childGuard
    simpa only [d693, d545, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8199 (pattern : Twelve) (guard : d0 pattern = 1) : d159 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8200 (pattern : Twelve) (guard : d1867 pattern = 1) : d159 pattern ≤ (0 : Int) + d492 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7815 pattern childGuard
    simpa only [d1867, d492, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8199 pattern childGuard
    simpa only [d1867, d492, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8201 (pattern : Twelve) (guard : d1867 pattern = 1) : d666 pattern ≤ (0 : Int) + d518 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d666, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d666, d518, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d666, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8200 pattern childGuard
    simpa only [d666, d518, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8202 (pattern : Twelve) (guard : d1867 pattern = 1) : d694 pattern ≤ (0 : Int) + d546 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d694, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8197 pattern childGuard
    simpa only [d694, d546, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d694, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8201 pattern childGuard
    simpa only [d694, d546, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8203 (pattern : Twelve) (guard : d1867 pattern = 1) : d717 pattern ≤ (0 : Int) + d569 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d717, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8198 pattern childGuard
    simpa only [d717, d569, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d717, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8202 pattern childGuard
    simpa only [d717, d569, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8204 (pattern : Twelve) (guard : d1867 pattern = 1) : d695 pattern ≤ (0 : Int) + d547 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d695, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8197 pattern childGuard
    simpa only [d695, d547, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d695, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d695, d547, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8205 (pattern : Twelve) (guard : d1867 pattern = 1) : d718 pattern ≤ (0 : Int) + d570 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d718, d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8204 pattern childGuard
    simpa only [d718, d570, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d718, d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8165 pattern childGuard
    simpa only [d718, d570, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8206 (pattern : Twelve) (guard : d1867 pattern = 1) : d740 pattern ≤ (0 : Int) + d592 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d740, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8203 pattern childGuard
    simpa only [d740, d592, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d740, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8205 pattern childGuard
    simpa only [d740, d592, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8207 (pattern : Twelve) (guard : d0 pattern = 1) : d160 pattern ≤ (0 : Int) + d14 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8208 (pattern : Twelve) (guard : d1867 pattern = 1) : d643 pattern ≤ (0 : Int) + d493 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d643, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7823 pattern childGuard
    simpa only [d1867, d643, d493, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d643, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8207 pattern childGuard
    simpa only [d1867, d643, d493, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8209 (pattern : Twelve) (guard : d1867 pattern = 1) : d13 pattern ≤ (0 : Int) + d494 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7825 pattern childGuard
    simpa only [d1867, d494, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2866 pattern childGuard
    simpa only [d1867, d494, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8210 (pattern : Twelve) (guard : d1867 pattern = 1) : d667 pattern ≤ (0 : Int) + d519 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d667, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8208 pattern childGuard
    simpa only [d667, d519, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d667, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8209 pattern childGuard
    simpa only [d667, d519, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8211 (pattern : Twelve) (guard : d1867 pattern = 1) : d668 pattern ≤ (0 : Int) + d520 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d668, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8156 pattern childGuard
    simpa only [d668, d520, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d668, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d668, d520, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8212 (pattern : Twelve) (guard : d1867 pattern = 1) : d696 pattern ≤ (0 : Int) + d548 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d696, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8210 pattern childGuard
    simpa only [d696, d548, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d696, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8211 pattern childGuard
    simpa only [d696, d548, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8213 (pattern : Twelve) (guard : d1867 pattern = 1) : d669 pattern ≤ (0 : Int) + d521 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d669, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8156 pattern childGuard
    simpa only [d669, d521, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d669, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8209 pattern childGuard
    simpa only [d669, d521, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8214 (pattern : Twelve) (guard : d1867 pattern = 1) : d697 pattern ≤ (0 : Int) + d549 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d697, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8213 pattern childGuard
    simpa only [d697, d549, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d697, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8211 pattern childGuard
    simpa only [d697, d549, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8215 (pattern : Twelve) (guard : d1867 pattern = 1) : d719 pattern ≤ (0 : Int) + d571 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d719, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8212 pattern childGuard
    simpa only [d719, d571, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d719, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8214 pattern childGuard
    simpa only [d719, d571, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8216 (pattern : Twelve) (guard : d1867 pattern = 1) : d644 pattern ≤ (0 : Int) + d495 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d644, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7837 pattern childGuard
    simpa only [d1867, d644, d495, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d644, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8199 pattern childGuard
    simpa only [d1867, d644, d495, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8217 (pattern : Twelve) (guard : d1867 pattern = 1) : d670 pattern ≤ (0 : Int) + d522 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d670, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8216 pattern childGuard
    simpa only [d670, d522, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d670, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d670, d522, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8218 (pattern : Twelve) (guard : d1867 pattern = 1) : d698 pattern ≤ (0 : Int) + d550 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d698, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8213 pattern childGuard
    simpa only [d698, d550, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d698, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8217 pattern childGuard
    simpa only [d698, d550, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8219 (pattern : Twelve) (guard : d1867 pattern = 1) : d720 pattern ≤ (0 : Int) + d572 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d720, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8214 pattern childGuard
    simpa only [d720, d572, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d720, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8218 pattern childGuard
    simpa only [d720, d572, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8220 (pattern : Twelve) (guard : d1867 pattern = 1) : d741 pattern ≤ (0 : Int) + d593 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d741, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8215 pattern childGuard
    simpa only [d741, d593, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d741, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8219 pattern childGuard
    simpa only [d741, d593, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8221 (pattern : Twelve) (guard : d1867 pattern = 1) : d756 pattern ≤ (0 : Int) + d608 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d756, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8206 pattern childGuard
    simpa only [d756, d608, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d756, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8220 pattern childGuard
    simpa only [d756, d608, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8222 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (0 : Int) + d14 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8223 (pattern : Twelve) (guard : d1867 pattern = 1) : d645 pattern ≤ (0 : Int) + d496 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d645, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7845 pattern childGuard
    simpa only [d1867, d645, d496, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d645, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8222 pattern childGuard
    simpa only [d1867, d645, d496, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8224 (pattern : Twelve) (guard : d1867 pattern = 1) : d671 pattern ≤ (0 : Int) + d523 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d671, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8223 pattern childGuard
    simpa only [d671, d523, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d671, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8156 pattern childGuard
    simpa only [d671, d523, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8225 (pattern : Twelve) (guard : d1867 pattern = 1) : d699 pattern ≤ (0 : Int) + d551 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d699, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8224 pattern childGuard
    simpa only [d699, d551, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d699, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8184 pattern childGuard
    simpa only [d699, d551, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8226 (pattern : Twelve) (guard : d1867 pattern = 1) : d721 pattern ≤ (0 : Int) + d573 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d721, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8225 pattern childGuard
    simpa only [d721, d573, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d721, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8186 pattern childGuard
    simpa only [d721, d573, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8227 (pattern : Twelve) (guard : d1867 pattern = 1) : d742 pattern ≤ (0 : Int) + d594 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d742, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8226 pattern childGuard
    simpa only [d742, d594, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d742, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8188 pattern childGuard
    simpa only [d742, d594, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8228 (pattern : Twelve) (guard : d1867 pattern = 1) : d757 pattern ≤ (0 : Int) + d609 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d757, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8227 pattern childGuard
    simpa only [d757, d609, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d757, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d757, d609, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8229 (pattern : Twelve) (guard : d1867 pattern = 1) : d767 pattern ≤ (0 : Int) + d619 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d767, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8221 pattern childGuard
    simpa only [d767, d619, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d767, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8228 pattern childGuard
    simpa only [d767, d619, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8230 (pattern : Twelve) (guard : d1867 pattern = 1) : d772 pattern ≤ (0 : Int) + d624 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d772, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8191 pattern childGuard
    simpa only [d772, d624, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d772, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8229 pattern childGuard
    simpa only [d772, d624, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8231 (pattern : Twelve) (guard : d1867 pattern = 1) : d722 pattern ≤ (0 : Int) + d574 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d722, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d722, d574, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d722, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8175 pattern childGuard
    simpa only [d722, d574, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8232 (pattern : Twelve) (guard : d1867 pattern = 1) : d672 pattern ≤ (0 : Int) + d524 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d672, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d672, d524, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d672, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8139 pattern childGuard
    simpa only [d672, d524, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8233 (pattern : Twelve) (guard : d1867 pattern = 1) : d700 pattern ≤ (0 : Int) + d552 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d700, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8232 pattern childGuard
    simpa only [d700, d552, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d700, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8142 pattern childGuard
    simpa only [d700, d552, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8234 (pattern : Twelve) (guard : d1867 pattern = 1) : d723 pattern ≤ (0 : Int) + d575 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d723, d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d723, d575, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d723, d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8233 pattern childGuard
    simpa only [d723, d575, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8235 (pattern : Twelve) (guard : d1867 pattern = 1) : d743 pattern ≤ (0 : Int) + d595 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d743, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8231 pattern childGuard
    simpa only [d743, d595, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d743, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8234 pattern childGuard
    simpa only [d743, d595, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8236 (pattern : Twelve) (guard : d1867 pattern = 1) : d673 pattern ≤ (0 : Int) + d525 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d673, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d673, d525, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d673, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8153 pattern childGuard
    simpa only [d673, d525, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8237 (pattern : Twelve) (guard : d1867 pattern = 1) : d701 pattern ≤ (0 : Int) + d553 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d701, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d701, d553, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d701, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8236 pattern childGuard
    simpa only [d701, d553, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8238 (pattern : Twelve) (guard : d1867 pattern = 1) : d702 pattern ≤ (0 : Int) + d554 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d702, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d702, d554, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d702, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8159 pattern childGuard
    simpa only [d702, d554, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8239 (pattern : Twelve) (guard : d1867 pattern = 1) : d724 pattern ≤ (0 : Int) + d576 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d724, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8237 pattern childGuard
    simpa only [d724, d576, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d724, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8238 pattern childGuard
    simpa only [d724, d576, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8240 (pattern : Twelve) (guard : d1867 pattern = 1) : d703 pattern ≤ (0 : Int) + d555 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d703, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d703, d555, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d703, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8162 pattern childGuard
    simpa only [d703, d555, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8241 (pattern : Twelve) (guard : d1867 pattern = 1) : d725 pattern ≤ (0 : Int) + d577 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d725, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8240 pattern childGuard
    simpa only [d725, d577, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d725, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8165 pattern childGuard
    simpa only [d725, d577, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8242 (pattern : Twelve) (guard : d1867 pattern = 1) : d744 pattern ≤ (0 : Int) + d596 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d744, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8239 pattern childGuard
    simpa only [d744, d596, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d744, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8241 pattern childGuard
    simpa only [d744, d596, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8243 (pattern : Twelve) (guard : d1867 pattern = 1) : d758 pattern ≤ (0 : Int) + d610 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d758, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8235 pattern childGuard
    simpa only [d758, d610, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d758, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8242 pattern childGuard
    simpa only [d758, d610, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8244 (pattern : Twelve) (guard : d1867 pattern = 1) : d726 pattern ≤ (0 : Int) + d578 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d726, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d726, d578, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d726, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8165 pattern childGuard
    simpa only [d726, d578, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8245 (pattern : Twelve) (guard : d1867 pattern = 1) : d745 pattern ≤ (0 : Int) + d597 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d745, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8231 pattern childGuard
    simpa only [d745, d597, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d745, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8244 pattern childGuard
    simpa only [d745, d597, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8246 (pattern : Twelve) (guard : d1867 pattern = 1) : d746 pattern ≤ (0 : Int) + d598 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d746, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8186 pattern childGuard
    simpa only [d746, d598, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d746, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8188 pattern childGuard
    simpa only [d746, d598, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8247 (pattern : Twelve) (guard : d1867 pattern = 1) : d759 pattern ≤ (0 : Int) + d611 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d759, d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8245 pattern childGuard
    simpa only [d759, d611, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d759, d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8246 pattern childGuard
    simpa only [d759, d611, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8248 (pattern : Twelve) (guard : d1867 pattern = 1) : d768 pattern ≤ (0 : Int) + d620 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d768, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8243 pattern childGuard
    simpa only [d768, d620, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d768, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8247 pattern childGuard
    simpa only [d768, d620, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8249 (pattern : Twelve) (guard : d1867 pattern = 1) : d704 pattern ≤ (0 : Int) + d556 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d704, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d704, d556, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d704, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8201 pattern childGuard
    simpa only [d704, d556, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8250 (pattern : Twelve) (guard : d1867 pattern = 1) : d727 pattern ≤ (0 : Int) + d579 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d727, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d727, d579, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d727, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8249 pattern childGuard
    simpa only [d727, d579, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8251 (pattern : Twelve) (guard : d1867 pattern = 1) : d728 pattern ≤ (0 : Int) + d580 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d728, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d728, d580, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d728, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8165 pattern childGuard
    simpa only [d728, d580, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8252 (pattern : Twelve) (guard : d1867 pattern = 1) : d747 pattern ≤ (0 : Int) + d599 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d747, d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8250 pattern childGuard
    simpa only [d747, d599, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d747, d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8251 pattern childGuard
    simpa only [d747, d599, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8253 (pattern : Twelve) (guard : d1867 pattern = 1) : d748 pattern ≤ (0 : Int) + d600 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d748, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8214 pattern childGuard
    simpa only [d748, d600, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d748, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8219 pattern childGuard
    simpa only [d748, d600, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8254 (pattern : Twelve) (guard : d1867 pattern = 1) : d760 pattern ≤ (0 : Int) + d612 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d760, d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8252 pattern childGuard
    simpa only [d760, d612, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d760, d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8253 pattern childGuard
    simpa only [d760, d612, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8255 (pattern : Twelve) (guard : d1867 pattern = 1) : d761 pattern ≤ (0 : Int) + d613 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d761, d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8246 pattern childGuard
    simpa only [d761, d613, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d761, d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d761, d613, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8256 (pattern : Twelve) (guard : d1867 pattern = 1) : d769 pattern ≤ (0 : Int) + d621 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d769, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8254 pattern childGuard
    simpa only [d769, d621, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d769, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8255 pattern childGuard
    simpa only [d769, d621, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8257 (pattern : Twelve) (guard : d1867 pattern = 1) : d773 pattern ≤ (0 : Int) + d625 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d773, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8248 pattern childGuard
    simpa only [d773, d625, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d773, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8256 pattern childGuard
    simpa only [d773, d625, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8258 (pattern : Twelve) (guard : d1867 pattern = 1) : d775 pattern ≤ (0 : Int) + d627 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d775, d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8230 pattern childGuard
    simpa only [d775, d627, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d775, d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8257 pattern childGuard
    simpa only [d775, d627, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8259 (pattern : Twelve) (guard : d1867 pattern = 1) : d776 pattern ≤ (0 : Int) + d628 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d776, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8258 pattern childGuard
    simpa only [d776, d628, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d776, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8257 pattern childGuard
    simpa only [d776, d628, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
