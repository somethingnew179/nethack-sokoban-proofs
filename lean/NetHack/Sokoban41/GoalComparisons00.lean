/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GoalDiagram
import NetHack.Sokoban41.Comparisons35
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem goalC0 (pattern : Ten) (guard : d786 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem goalC1 (pattern : Ten) (guard : d359 pattern = 1) : d0 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) ≤ (0 : Int) + 4
  decide
theorem goalC2 (pattern : Ten) (guard : d787 pattern = 1) : d0 pattern ≤ (0 : Int) + d86 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d786 pattern = 1 := by simpa only [d787, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC0 pattern childGuard
    simpa only [d787, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d787, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1 pattern childGuard
    simpa only [d787, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC3 (pattern : Ten) (guard : d606 pattern = 1) : d12 pattern ≤ (0 : Int) + d801 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d12, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5259 pattern childGuard
    simpa only [d606, d12, d801, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d12, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5 pattern childGuard
    simpa only [d606, d12, d801, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC4 (pattern : Ten) (guard : d788 pattern = 1) : d17 pattern ≤ (0 : Int) + d802 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d787 pattern = 1 := by simpa only [d788, d17, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC2 pattern childGuard
    simpa only [d788, d17, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d606 pattern = 1 := by simpa only [d788, d17, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC3 pattern childGuard
    simpa only [d788, d17, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC5 (pattern : Ten) (guard : d606 pattern = 1) : d12 pattern ≤ (0 : Int) + d43 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d12, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5159 pattern childGuard
    simpa only [d606, d12, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d12, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d606, d12, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC6 (pattern : Ten) (guard : d607 pattern = 1) : d18 pattern ≤ (0 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d18, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC5 pattern childGuard
    simpa only [d607, d18, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d18, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d607, d18, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC7 (pattern : Ten) (guard : d789 pattern = 1) : d23 pattern ≤ (0 : Int) + d803 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d788 pattern = 1 := by simpa only [d789, d23, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC4 pattern childGuard
    simpa only [d789, d23, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d607 pattern = 1 := by simpa only [d789, d23, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC6 pattern childGuard
    simpa only [d789, d23, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC8 (pattern : Ten) (guard : d606 pattern = 1) : d13 pattern ≤ (0 : Int) + d68 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d13, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d606, d13, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d13, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c462 pattern childGuard
    simpa only [d606, d13, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC9 (pattern : Ten) (guard : d607 pattern = 1) : d19 pattern ≤ (0 : Int) + d70 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d19, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC8 pattern childGuard
    simpa only [d607, d19, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d19, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c644 pattern childGuard
    simpa only [d607, d19, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC10 (pattern : Ten) (guard : d608 pattern = 1) : d24 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d24, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC9 pattern childGuard
    simpa only [d608, d24, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d24, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c789 pattern childGuard
    simpa only [d608, d24, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC11 (pattern : Ten) (guard : d790 pattern = 1) : d29 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d789 pattern = 1 := by simpa only [d790, d29, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC7 pattern childGuard
    simpa only [d790, d29, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d790, d29, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC10 pattern childGuard
    simpa only [d790, d29, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC12 (pattern : Ten) (guard : d606 pattern = 1) : d15 pattern ≤ (0 : Int) + d805 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d15, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4781 pattern childGuard
    simpa only [d606, d15, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d15, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c469 pattern childGuard
    simpa only [d606, d15, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC13 (pattern : Ten) (guard : d0 pattern = 1) : d16 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC14 (pattern : Ten) (guard : d607 pattern = 1) : d21 pattern ≤ (0 : Int) + d806 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d21, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC12 pattern childGuard
    simpa only [d607, d21, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d21, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC13 pattern childGuard
    simpa only [d607, d21, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC15 (pattern : Ten) (guard : d0 pattern = 1) : d22 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC16 (pattern : Ten) (guard : d608 pattern = 1) : d25 pattern ≤ (0 : Int) + d807 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d25, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC14 pattern childGuard
    simpa only [d608, d25, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d25, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC15 pattern childGuard
    simpa only [d608, d25, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC17 (pattern : Ten) (guard : d0 pattern = 1) : d24 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC18 (pattern : Ten) (guard : d609 pattern = 1) : d30 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d30, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC16 pattern childGuard
    simpa only [d609, d30, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d30, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC17 pattern childGuard
    simpa only [d609, d30, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC19 (pattern : Ten) (guard : d791 pattern = 1) : d33 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d790 pattern = 1 := by simpa only [d791, d33, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC11 pattern childGuard
    simpa only [d791, d33, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d791, d33, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC18 pattern childGuard
    simpa only [d791, d33, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC20 (pattern : Ten) (guard : d606 pattern = 1) : d12 pattern ≤ (0 : Int) + d45 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d12, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4953 pattern childGuard
    simpa only [d606, d12, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d12, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d606, d12, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC21 (pattern : Ten) (guard : d607 pattern = 1) : d18 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d18, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC20 pattern childGuard
    simpa only [d607, d18, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d18, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d607, d18, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC22 (pattern : Ten) (guard : d608 pattern = 1) : d26 pattern ≤ (0 : Int) + d810 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d26, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC21 pattern childGuard
    simpa only [d608, d26, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d26, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d608, d26, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC23 (pattern : Ten) (guard : d609 pattern = 1) : d31 pattern ≤ (0 : Int) + d811 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d31, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC22 pattern childGuard
    simpa only [d609, d31, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d31, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1267 pattern childGuard
    simpa only [d609, d31, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC24 (pattern : Ten) (guard : d0 pattern = 1) : d32 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC25 (pattern : Ten) (guard : d610 pattern = 1) : d34 pattern ≤ (0 : Int) + d812 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d34, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC23 pattern childGuard
    simpa only [d610, d34, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d34, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC24 pattern childGuard
    simpa only [d610, d34, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC26 (pattern : Ten) (guard : d792 pattern = 1) : d35 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d791 pattern = 1 := by simpa only [d792, d35, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC19 pattern childGuard
    simpa only [d792, d35, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d792, d35, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC25 pattern childGuard
    simpa only [d792, d35, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC27 (pattern : Ten) (guard : d606 pattern = 1) : d12 pattern ≤ (0 : Int) + d805 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d12, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4781 pattern childGuard
    simpa only [d606, d12, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d12, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d606, d12, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC28 (pattern : Ten) (guard : d607 pattern = 1) : d18 pattern ≤ (0 : Int) + d806 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d18, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC27 pattern childGuard
    simpa only [d607, d18, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d18, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d607, d18, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC29 (pattern : Ten) (guard : d608 pattern = 1) : d26 pattern ≤ (0 : Int) + d807 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d26, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC28 pattern childGuard
    simpa only [d608, d26, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d26, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d608, d26, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC30 (pattern : Ten) (guard : d609 pattern = 1) : d31 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d31, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC29 pattern childGuard
    simpa only [d609, d31, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d31, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1267 pattern childGuard
    simpa only [d609, d31, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC31 (pattern : Ten) (guard : d610 pattern = 1) : d34 pattern ≤ (0 : Int) + d814 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d34, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC30 pattern childGuard
    simpa only [d610, d34, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d34, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC24 pattern childGuard
    simpa only [d610, d34, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC32 (pattern : Ten) (guard : d611 pattern = 1) : d36 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d36, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC31 pattern childGuard
    simpa only [d611, d36, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d36, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d611, d36, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC33 (pattern : Ten) (guard : d793 pattern = 1) : d37 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d792 pattern = 1 := by simpa only [d793, d37, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC26 pattern childGuard
    simpa only [d793, d37, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d793, d37, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC32 pattern childGuard
    simpa only [d793, d37, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC34 (pattern : Ten) (guard : d787 pattern = 1) : d15 pattern ≤ (0 : Int) + d86 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d786 pattern = 1 := by simpa only [d787, d15, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC0 pattern childGuard
    simpa only [d787, d15, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d787, d15, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5375 pattern childGuard
    simpa only [d787, d15, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC35 (pattern : Ten) (guard : d606 pattern = 1) : d42 pattern ≤ (0 : Int) + d801 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d42, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5274 pattern childGuard
    simpa only [d606, d42, d801, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d42, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5 pattern childGuard
    simpa only [d606, d42, d801, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC36 (pattern : Ten) (guard : d788 pattern = 1) : d48 pattern ≤ (0 : Int) + d802 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d787 pattern = 1 := by simpa only [d788, d48, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC34 pattern childGuard
    simpa only [d788, d48, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d606 pattern = 1 := by simpa only [d788, d48, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC35 pattern childGuard
    simpa only [d788, d48, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC37 (pattern : Ten) (guard : d607 pattern = 1) : d49 pattern ≤ (0 : Int) + d49 pattern := by
  omega
theorem goalC38 (pattern : Ten) (guard : d789 pattern = 1) : d54 pattern ≤ (0 : Int) + d803 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d788 pattern = 1 := by simpa only [d789, d54, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC36 pattern childGuard
    simpa only [d789, d54, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d607 pattern = 1 := by simpa only [d789, d54, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC37 pattern childGuard
    simpa only [d789, d54, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC39 (pattern : Ten) (guard : d606 pattern = 1) : d15 pattern ≤ (0 : Int) + d68 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d15, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d606, d15, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d15, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c469 pattern childGuard
    simpa only [d606, d15, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC40 (pattern : Ten) (guard : d0 pattern = 1) : d42 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC41 (pattern : Ten) (guard : d607 pattern = 1) : d48 pattern ≤ (0 : Int) + d70 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d48, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC39 pattern childGuard
    simpa only [d607, d48, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d48, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC40 pattern childGuard
    simpa only [d607, d48, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC42 (pattern : Ten) (guard : d0 pattern = 1) : d49 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC43 (pattern : Ten) (guard : d608 pattern = 1) : d54 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d54, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC41 pattern childGuard
    simpa only [d608, d54, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d54, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC42 pattern childGuard
    simpa only [d608, d54, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC44 (pattern : Ten) (guard : d790 pattern = 1) : d54 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d789 pattern = 1 := by simpa only [d790, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC38 pattern childGuard
    simpa only [d790, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d790, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC43 pattern childGuard
    simpa only [d790, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC45 (pattern : Ten) (guard : d607 pattern = 1) : d48 pattern ≤ (0 : Int) + d806 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d48, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC12 pattern childGuard
    simpa only [d607, d48, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d48, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC40 pattern childGuard
    simpa only [d607, d48, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC46 (pattern : Ten) (guard : d608 pattern = 1) : d54 pattern ≤ (0 : Int) + d807 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d54, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC45 pattern childGuard
    simpa only [d608, d54, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d54, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC42 pattern childGuard
    simpa only [d608, d54, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC47 (pattern : Ten) (guard : d609 pattern = 1) : d54 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC46 pattern childGuard
    simpa only [d609, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1185 pattern childGuard
    simpa only [d609, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC48 (pattern : Ten) (guard : d791 pattern = 1) : d54 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d790 pattern = 1 := by simpa only [d791, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC44 pattern childGuard
    simpa only [d791, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d791, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC47 pattern childGuard
    simpa only [d791, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC49 (pattern : Ten) (guard : d606 pattern = 1) : d15 pattern ≤ (0 : Int) + d45 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d15, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4953 pattern childGuard
    simpa only [d606, d15, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d15, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c469 pattern childGuard
    simpa only [d606, d15, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC50 (pattern : Ten) (guard : d607 pattern = 1) : d48 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d48, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC49 pattern childGuard
    simpa only [d607, d48, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d48, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC40 pattern childGuard
    simpa only [d607, d48, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC51 (pattern : Ten) (guard : d608 pattern = 1) : d54 pattern ≤ (0 : Int) + d810 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d54, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC50 pattern childGuard
    simpa only [d608, d54, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d54, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC42 pattern childGuard
    simpa only [d608, d54, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC52 (pattern : Ten) (guard : d609 pattern = 1) : d58 pattern ≤ (0 : Int) + d811 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d58, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC51 pattern childGuard
    simpa only [d609, d58, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d58, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1267 pattern childGuard
    simpa only [d609, d58, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC53 (pattern : Ten) (guard : d0 pattern = 1) : d59 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC54 (pattern : Ten) (guard : d610 pattern = 1) : d62 pattern ≤ (0 : Int) + d812 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d62, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC52 pattern childGuard
    simpa only [d610, d62, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d62, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC53 pattern childGuard
    simpa only [d610, d62, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC55 (pattern : Ten) (guard : d792 pattern = 1) : d64 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d791 pattern = 1 := by simpa only [d792, d64, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC48 pattern childGuard
    simpa only [d792, d64, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d792, d64, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC54 pattern childGuard
    simpa only [d792, d64, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC56 (pattern : Ten) (guard : d606 pattern = 1) : d46 pattern ≤ (0 : Int) + d805 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d46, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4891 pattern childGuard
    simpa only [d606, d46, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d46, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d606, d46, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC57 (pattern : Ten) (guard : d607 pattern = 1) : d52 pattern ≤ (0 : Int) + d806 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d52, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC56 pattern childGuard
    simpa only [d607, d52, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d52, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d607, d52, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC58 (pattern : Ten) (guard : d608 pattern = 1) : d56 pattern ≤ (0 : Int) + d807 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d56, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC57 pattern childGuard
    simpa only [d608, d56, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d56, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d608, d56, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC59 (pattern : Ten) (guard : d609 pattern = 1) : d56 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC58 pattern childGuard
    simpa only [d609, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1152 pattern childGuard
    simpa only [d609, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC60 (pattern : Ten) (guard : d610 pattern = 1) : d56 pattern ≤ (0 : Int) + d814 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC59 pattern childGuard
    simpa only [d610, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1152 pattern childGuard
    simpa only [d610, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC61 (pattern : Ten) (guard : d0 pattern = 1) : d63 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC62 (pattern : Ten) (guard : d611 pattern = 1) : d65 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d65, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC60 pattern childGuard
    simpa only [d611, d65, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d65, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC61 pattern childGuard
    simpa only [d611, d65, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC63 (pattern : Ten) (guard : d793 pattern = 1) : d66 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d792 pattern = 1 := by simpa only [d793, d66, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC55 pattern childGuard
    simpa only [d793, d66, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d793, d66, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC62 pattern childGuard
    simpa only [d793, d66, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC64 (pattern : Ten) (guard : d606 pattern = 1) : d67 pattern ≤ (0 : Int) + d68 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d67, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d606, d67, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d67, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c109 pattern childGuard
    simpa only [d606, d67, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC65 (pattern : Ten) (guard : d0 pattern = 1) : d68 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC66 (pattern : Ten) (guard : d607 pattern = 1) : d69 pattern ≤ (0 : Int) + d70 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d69, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC64 pattern childGuard
    simpa only [d607, d69, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d69, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC65 pattern childGuard
    simpa only [d607, d69, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC67 (pattern : Ten) (guard : d0 pattern = 1) : d70 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC68 (pattern : Ten) (guard : d608 pattern = 1) : d71 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d71, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC66 pattern childGuard
    simpa only [d608, d71, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d71, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC67 pattern childGuard
    simpa only [d608, d71, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC69 (pattern : Ten) (guard : d790 pattern = 1) : d73 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d789 pattern = 1 := by simpa only [d790, d73, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC7 pattern childGuard
    simpa only [d790, d73, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d790, d73, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC68 pattern childGuard
    simpa only [d790, d73, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC70 (pattern : Ten) (guard : d0 pattern = 1) : d71 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC71 (pattern : Ten) (guard : d609 pattern = 1) : d74 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d74, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC16 pattern childGuard
    simpa only [d609, d74, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d74, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC70 pattern childGuard
    simpa only [d609, d74, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC72 (pattern : Ten) (guard : d791 pattern = 1) : d77 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d790 pattern = 1 := by simpa only [d791, d77, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC69 pattern childGuard
    simpa only [d791, d77, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d791, d77, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC71 pattern childGuard
    simpa only [d791, d77, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC73 (pattern : Ten) (guard : d0 pattern = 1) : d72 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC74 (pattern : Ten) (guard : d609 pattern = 1) : d75 pattern ≤ (0 : Int) + d811 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d75, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC22 pattern childGuard
    simpa only [d609, d75, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d75, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC73 pattern childGuard
    simpa only [d609, d75, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC75 (pattern : Ten) (guard : d0 pattern = 1) : d76 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC76 (pattern : Ten) (guard : d610 pattern = 1) : d78 pattern ≤ (0 : Int) + d812 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d78, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC74 pattern childGuard
    simpa only [d610, d78, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d78, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC75 pattern childGuard
    simpa only [d610, d78, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC77 (pattern : Ten) (guard : d792 pattern = 1) : d79 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d791 pattern = 1 := by simpa only [d792, d79, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC72 pattern childGuard
    simpa only [d792, d79, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d792, d79, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC76 pattern childGuard
    simpa only [d792, d79, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC78 (pattern : Ten) (guard : d609 pattern = 1) : d75 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d75, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC29 pattern childGuard
    simpa only [d609, d75, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d75, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC73 pattern childGuard
    simpa only [d609, d75, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC79 (pattern : Ten) (guard : d610 pattern = 1) : d78 pattern ≤ (0 : Int) + d814 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d78, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC78 pattern childGuard
    simpa only [d610, d78, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d78, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC75 pattern childGuard
    simpa only [d610, d78, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC80 (pattern : Ten) (guard : d611 pattern = 1) : d80 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d80, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC79 pattern childGuard
    simpa only [d611, d80, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d80, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d611, d80, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC81 (pattern : Ten) (guard : d793 pattern = 1) : d81 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d792 pattern = 1 := by simpa only [d793, d81, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC77 pattern childGuard
    simpa only [d793, d81, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d793, d81, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC80 pattern childGuard
    simpa only [d793, d81, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC82 (pattern : Ten) (guard : d359 pattern = 1) : d7 pattern ≤ (0 : Int) + d7 pattern := by
  omega
theorem goalC83 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC84 (pattern : Ten) (guard : d606 pattern = 1) : d7 pattern ≤ (0 : Int) + d805 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC82 pattern childGuard
    simpa only [d606, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC83 pattern childGuard
    simpa only [d606, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC85 (pattern : Ten) (guard : d607 pattern = 1) : d7 pattern ≤ (0 : Int) + d806 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC84 pattern childGuard
    simpa only [d607, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC83 pattern childGuard
    simpa only [d607, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC86 (pattern : Ten) (guard : d608 pattern = 1) : d7 pattern ≤ (0 : Int) + d807 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC85 pattern childGuard
    simpa only [d608, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC83 pattern childGuard
    simpa only [d608, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC87 (pattern : Ten) (guard : d609 pattern = 1) : d7 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC86 pattern childGuard
    simpa only [d609, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC83 pattern childGuard
    simpa only [d609, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC88 (pattern : Ten) (guard : d791 pattern = 1) : d82 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d790 pattern = 1 := by simpa only [d791, d82, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC44 pattern childGuard
    simpa only [d791, d82, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d791, d82, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC87 pattern childGuard
    simpa only [d791, d82, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC89 (pattern : Ten) (guard : d0 pattern = 1) : d58 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC90 (pattern : Ten) (guard : d610 pattern = 1) : d58 pattern ≤ (0 : Int) + d812 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC52 pattern childGuard
    simpa only [d610, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC89 pattern childGuard
    simpa only [d610, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC91 (pattern : Ten) (guard : d792 pattern = 1) : d83 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d791 pattern = 1 := by simpa only [d792, d83, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC88 pattern childGuard
    simpa only [d792, d83, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d792, d83, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC90 pattern childGuard
    simpa only [d792, d83, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC92 (pattern : Ten) (guard : d0 pattern = 1) : d60 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC93 (pattern : Ten) (guard : d611 pattern = 1) : d84 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d84, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC60 pattern childGuard
    simpa only [d611, d84, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d84, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC92 pattern childGuard
    simpa only [d611, d84, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC94 (pattern : Ten) (guard : d793 pattern = 1) : d85 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d792 pattern = 1 := by simpa only [d793, d85, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC91 pattern childGuard
    simpa only [d793, d85, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d793, d85, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC93 pattern childGuard
    simpa only [d793, d85, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC95 (pattern : Ten) (guard : d787 pattern = 1) : d86 pattern ≤ (0 : Int) + d86 pattern := by
  omega
theorem goalC96 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC97 (pattern : Ten) (guard : d606 pattern = 1) : d0 pattern ≤ (0 : Int) + d801 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5259 pattern childGuard
    simpa only [d606, d801, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC96 pattern childGuard
    simpa only [d606, d801, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC98 (pattern : Ten) (guard : d788 pattern = 1) : d87 pattern ≤ (0 : Int) + d802 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d787 pattern = 1 := by simpa only [d788, d87, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC95 pattern childGuard
    simpa only [d788, d87, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d606 pattern = 1 := by simpa only [d788, d87, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC97 pattern childGuard
    simpa only [d788, d87, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC99 (pattern : Ten) (guard : d606 pattern = 1) : d0 pattern ≤ (0 : Int) + d43 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5159 pattern childGuard
    simpa only [d606, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c90 pattern childGuard
    simpa only [d606, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC100 (pattern : Ten) (guard : d607 pattern = 1) : d88 pattern ≤ (0 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d88, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC99 pattern childGuard
    simpa only [d607, d88, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d88, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d607, d88, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC101 (pattern : Ten) (guard : d789 pattern = 1) : d93 pattern ≤ (0 : Int) + d803 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d788 pattern = 1 := by simpa only [d789, d93, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC98 pattern childGuard
    simpa only [d789, d93, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d607 pattern = 1 := by simpa only [d789, d93, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC100 pattern childGuard
    simpa only [d789, d93, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC102 (pattern : Ten) (guard : d606 pattern = 1) : d0 pattern ≤ (0 : Int) + d68 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d606, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c90 pattern childGuard
    simpa only [d606, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC103 (pattern : Ten) (guard : d607 pattern = 1) : d89 pattern ≤ (0 : Int) + d70 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d89, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC102 pattern childGuard
    simpa only [d607, d89, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d89, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c462 pattern childGuard
    simpa only [d607, d89, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC104 (pattern : Ten) (guard : d0 pattern = 1) : d90 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC105 (pattern : Ten) (guard : d608 pattern = 1) : d94 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d94, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC103 pattern childGuard
    simpa only [d608, d94, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d94, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC104 pattern childGuard
    simpa only [d608, d94, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC106 (pattern : Ten) (guard : d790 pattern = 1) : d99 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d789 pattern = 1 := by simpa only [d790, d99, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC101 pattern childGuard
    simpa only [d790, d99, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d790, d99, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC105 pattern childGuard
    simpa only [d790, d99, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC107 (pattern : Ten) (guard : d606 pattern = 1) : d0 pattern ≤ (0 : Int) + d805 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4781 pattern childGuard
    simpa only [d606, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c90 pattern childGuard
    simpa only [d606, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC108 (pattern : Ten) (guard : d607 pattern = 1) : d91 pattern ≤ (0 : Int) + d806 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d91, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC107 pattern childGuard
    simpa only [d607, d91, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d91, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c469 pattern childGuard
    simpa only [d607, d91, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC109 (pattern : Ten) (guard : d0 pattern = 1) : d92 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC110 (pattern : Ten) (guard : d608 pattern = 1) : d95 pattern ≤ (0 : Int) + d807 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d95, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC108 pattern childGuard
    simpa only [d608, d95, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d95, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC109 pattern childGuard
    simpa only [d608, d95, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC111 (pattern : Ten) (guard : d0 pattern = 1) : d94 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC112 (pattern : Ten) (guard : d609 pattern = 1) : d100 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d100, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC110 pattern childGuard
    simpa only [d609, d100, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d100, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC111 pattern childGuard
    simpa only [d609, d100, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC113 (pattern : Ten) (guard : d791 pattern = 1) : d103 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d790 pattern = 1 := by simpa only [d791, d103, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC106 pattern childGuard
    simpa only [d791, d103, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d791, d103, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC112 pattern childGuard
    simpa only [d791, d103, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC114 (pattern : Ten) (guard : d606 pattern = 1) : d0 pattern ≤ (0 : Int) + d45 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4953 pattern childGuard
    simpa only [d606, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c90 pattern childGuard
    simpa only [d606, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC115 (pattern : Ten) (guard : d607 pattern = 1) : d88 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d88, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC114 pattern childGuard
    simpa only [d607, d88, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d88, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d607, d88, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC116 (pattern : Ten) (guard : d608 pattern = 1) : d96 pattern ≤ (0 : Int) + d810 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d96, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC115 pattern childGuard
    simpa only [d608, d96, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d96, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d608, d96, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC117 (pattern : Ten) (guard : d0 pattern = 1) : d97 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC118 (pattern : Ten) (guard : d609 pattern = 1) : d101 pattern ≤ (0 : Int) + d811 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d101, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC116 pattern childGuard
    simpa only [d609, d101, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d101, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC117 pattern childGuard
    simpa only [d609, d101, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC119 (pattern : Ten) (guard : d0 pattern = 1) : d102 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC120 (pattern : Ten) (guard : d610 pattern = 1) : d104 pattern ≤ (0 : Int) + d812 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d104, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC118 pattern childGuard
    simpa only [d610, d104, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d104, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC119 pattern childGuard
    simpa only [d610, d104, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC121 (pattern : Ten) (guard : d792 pattern = 1) : d105 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d791 pattern = 1 := by simpa only [d792, d105, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC113 pattern childGuard
    simpa only [d792, d105, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d792, d105, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC120 pattern childGuard
    simpa only [d792, d105, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC122 (pattern : Ten) (guard : d607 pattern = 1) : d88 pattern ≤ (0 : Int) + d806 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d88, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC107 pattern childGuard
    simpa only [d607, d88, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d88, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d607, d88, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC123 (pattern : Ten) (guard : d608 pattern = 1) : d96 pattern ≤ (0 : Int) + d807 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d96, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC122 pattern childGuard
    simpa only [d608, d96, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d96, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d608, d96, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC124 (pattern : Ten) (guard : d609 pattern = 1) : d101 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d101, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC123 pattern childGuard
    simpa only [d609, d101, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d101, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC117 pattern childGuard
    simpa only [d609, d101, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC125 (pattern : Ten) (guard : d610 pattern = 1) : d104 pattern ≤ (0 : Int) + d814 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d104, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC124 pattern childGuard
    simpa only [d610, d104, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d104, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC119 pattern childGuard
    simpa only [d610, d104, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC126 (pattern : Ten) (guard : d611 pattern = 1) : d106 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d106, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC125 pattern childGuard
    simpa only [d611, d106, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d106, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d611, d106, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC127 (pattern : Ten) (guard : d793 pattern = 1) : d107 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d792 pattern = 1 := by simpa only [d793, d107, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC121 pattern childGuard
    simpa only [d793, d107, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d793, d107, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC126 pattern childGuard
    simpa only [d793, d107, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC128 (pattern : Ten) (guard : d359 pattern = 1) : d5 pattern ≤ (0 : Int) + d5 pattern := by
  omega
theorem goalC129 (pattern : Ten) (guard : d0 pattern = 1) : d5 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC130 (pattern : Ten) (guard : d606 pattern = 1) : d5 pattern ≤ (0 : Int) + d801 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC128 pattern childGuard
    simpa only [d606, d801, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC129 pattern childGuard
    simpa only [d606, d801, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC131 (pattern : Ten) (guard : d788 pattern = 1) : d108 pattern ≤ (0 : Int) + d802 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d787 pattern = 1 := by simpa only [d788, d108, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC34 pattern childGuard
    simpa only [d788, d108, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d606 pattern = 1 := by simpa only [d788, d108, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC130 pattern childGuard
    simpa only [d788, d108, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC132 (pattern : Ten) (guard : d606 pattern = 1) : d15 pattern ≤ (0 : Int) + d43 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d15, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5159 pattern childGuard
    simpa only [d606, d15, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d15, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c469 pattern childGuard
    simpa only [d606, d15, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC133 (pattern : Ten) (guard : d607 pattern = 1) : d15 pattern ≤ (0 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC132 pattern childGuard
    simpa only [d607, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c688 pattern childGuard
    simpa only [d607, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC134 (pattern : Ten) (guard : d789 pattern = 1) : d109 pattern ≤ (0 : Int) + d803 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d788 pattern = 1 := by simpa only [d789, d109, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC131 pattern childGuard
    simpa only [d789, d109, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d607 pattern = 1 := by simpa only [d789, d109, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC133 pattern childGuard
    simpa only [d789, d109, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC135 (pattern : Ten) (guard : d607 pattern = 1) : d15 pattern ≤ (0 : Int) + d70 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC39 pattern childGuard
    simpa only [d607, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c688 pattern childGuard
    simpa only [d607, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC136 (pattern : Ten) (guard : d608 pattern = 1) : d110 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d110, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC135 pattern childGuard
    simpa only [d608, d110, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d110, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c644 pattern childGuard
    simpa only [d608, d110, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC137 (pattern : Ten) (guard : d790 pattern = 1) : d115 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d789 pattern = 1 := by simpa only [d790, d115, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC134 pattern childGuard
    simpa only [d790, d115, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d790, d115, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC136 pattern childGuard
    simpa only [d790, d115, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC138 (pattern : Ten) (guard : d607 pattern = 1) : d15 pattern ≤ (0 : Int) + d806 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC12 pattern childGuard
    simpa only [d607, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c688 pattern childGuard
    simpa only [d607, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC139 (pattern : Ten) (guard : d608 pattern = 1) : d111 pattern ≤ (0 : Int) + d807 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d111, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC138 pattern childGuard
    simpa only [d608, d111, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d111, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c699 pattern childGuard
    simpa only [d608, d111, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC140 (pattern : Ten) (guard : d0 pattern = 1) : d110 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC141 (pattern : Ten) (guard : d609 pattern = 1) : d116 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d116, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC139 pattern childGuard
    simpa only [d609, d116, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d116, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC140 pattern childGuard
    simpa only [d609, d116, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC142 (pattern : Ten) (guard : d791 pattern = 1) : d119 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d790 pattern = 1 := by simpa only [d791, d119, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC137 pattern childGuard
    simpa only [d791, d119, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d791, d119, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC141 pattern childGuard
    simpa only [d791, d119, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC143 (pattern : Ten) (guard : d607 pattern = 1) : d15 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC49 pattern childGuard
    simpa only [d607, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c688 pattern childGuard
    simpa only [d607, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC144 (pattern : Ten) (guard : d608 pattern = 1) : d112 pattern ≤ (0 : Int) + d810 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d112, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC143 pattern childGuard
    simpa only [d608, d112, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d112, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d608, d112, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC145 (pattern : Ten) (guard : d0 pattern = 1) : d113 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC146 (pattern : Ten) (guard : d609 pattern = 1) : d117 pattern ≤ (0 : Int) + d811 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d117, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC144 pattern childGuard
    simpa only [d609, d117, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d117, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC145 pattern childGuard
    simpa only [d609, d117, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC147 (pattern : Ten) (guard : d0 pattern = 1) : d118 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC148 (pattern : Ten) (guard : d610 pattern = 1) : d120 pattern ≤ (0 : Int) + d812 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d120, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC146 pattern childGuard
    simpa only [d610, d120, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d120, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC147 pattern childGuard
    simpa only [d610, d120, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC149 (pattern : Ten) (guard : d792 pattern = 1) : d121 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d791 pattern = 1 := by simpa only [d792, d121, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC142 pattern childGuard
    simpa only [d792, d121, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d792, d121, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC148 pattern childGuard
    simpa only [d792, d121, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC150 (pattern : Ten) (guard : d608 pattern = 1) : d112 pattern ≤ (0 : Int) + d807 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d112, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC138 pattern childGuard
    simpa only [d608, d112, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d112, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d608, d112, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC151 (pattern : Ten) (guard : d609 pattern = 1) : d117 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d117, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC150 pattern childGuard
    simpa only [d609, d117, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d117, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC145 pattern childGuard
    simpa only [d609, d117, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC152 (pattern : Ten) (guard : d610 pattern = 1) : d120 pattern ≤ (0 : Int) + d814 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d120, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC151 pattern childGuard
    simpa only [d610, d120, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d120, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC147 pattern childGuard
    simpa only [d610, d120, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC153 (pattern : Ten) (guard : d611 pattern = 1) : d122 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d122, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC152 pattern childGuard
    simpa only [d611, d122, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d122, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d611, d122, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC154 (pattern : Ten) (guard : d793 pattern = 1) : d123 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d792 pattern = 1 := by simpa only [d793, d123, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC149 pattern childGuard
    simpa only [d793, d123, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d793, d123, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC153 pattern childGuard
    simpa only [d793, d123, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC155 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC156 (pattern : Ten) (guard : d606 pattern = 1) : d6 pattern ≤ (0 : Int) + d43 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5173 pattern childGuard
    simpa only [d606, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC155 pattern childGuard
    simpa only [d606, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC157 (pattern : Ten) (guard : d607 pattern = 1) : d6 pattern ≤ (0 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC156 pattern childGuard
    simpa only [d607, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC155 pattern childGuard
    simpa only [d607, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC158 (pattern : Ten) (guard : d789 pattern = 1) : d124 pattern ≤ (0 : Int) + d803 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d788 pattern = 1 := by simpa only [d789, d124, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC36 pattern childGuard
    simpa only [d789, d124, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d607 pattern = 1 := by simpa only [d789, d124, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC157 pattern childGuard
    simpa only [d789, d124, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC159 (pattern : Ten) (guard : d608 pattern = 1) : d48 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC41 pattern childGuard
    simpa only [d608, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c826 pattern childGuard
    simpa only [d608, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
