/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons097
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c13720 (pattern : Twelve) (guard : d1835 pattern = 1) : d225 pattern ≤ (4 : Int) + d864 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13718 pattern childGuard
    simpa only [d1835, d225, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13719 pattern childGuard
    simpa only [d1835, d225, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13721 (pattern : Twelve) (guard : d2266 pattern = 1) : d229 pattern ≤ (4 : Int) + d864 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13695 pattern childGuard
    simpa only [d2266, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13720 pattern childGuard
    simpa only [d2266, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13722 (pattern : Twelve) (guard : d2266 pattern = 1) : d231 pattern ≤ (4 : Int) + d2268 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2266 pattern = 1 := by simpa only [d231, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13694 pattern childGuard
    simpa only [d231, d2268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2266 pattern = 1 := by simpa only [d231, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13721 pattern childGuard
    simpa only [d231, d2268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13723 (pattern : Twelve) (guard : d0 pattern = 1) : d226 pattern ≤ (4 : Int) + d861 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13724 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (4 : Int) + d861 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13725 (pattern : Twelve) (guard : d1835 pattern = 1) : d227 pattern ≤ (4 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13691 pattern childGuard
    simpa only [d1835, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13724 pattern childGuard
    simpa only [d1835, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13726 (pattern : Twelve) (guard : d2266 pattern = 1) : d230 pattern ≤ (4 : Int) + d861 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13723 pattern childGuard
    simpa only [d2266, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13725 pattern childGuard
    simpa only [d2266, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13727 (pattern : Twelve) (guard : d2266 pattern = 1) : d232 pattern ≤ (4 : Int) + d2268 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2266 pattern = 1 := by simpa only [d232, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13726 pattern childGuard
    simpa only [d232, d2268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2266 pattern = 1 := by simpa only [d232, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13721 pattern childGuard
    simpa only [d232, d2268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13728 (pattern : Twelve) (guard : d2266 pattern = 1) : d233 pattern ≤ (4 : Int) + d2268 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2266 pattern = 1 := by simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13722 pattern childGuard
    simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2266 pattern = 1 := by simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13727 pattern childGuard
    simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13729 (pattern : Twelve) (guard : d2266 pattern = 1) : d234 pattern ≤ (4 : Int) + d2268 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2266 pattern = 1 := by simpa only [d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13728 pattern childGuard
    simpa only [d234, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2266 pattern = 1 := by simpa only [d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13727 pattern childGuard
    simpa only [d234, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13730 (pattern : Twelve) (guard : d0 pattern = 1) : d927 pattern ≤ (4 : Int) + d1313 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13731 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (4 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13629 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10460 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13732 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (4 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13630 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13731 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13733 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (4 : Int) + d2 pattern := by
  change (3 : Int) ≤ (4 : Int) + 2
  decide
theorem c13734 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (4 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13632 pattern childGuard
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13733 pattern childGuard
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13735 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (4 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13632 pattern childGuard
    simpa only [d23, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13734 pattern childGuard
    simpa only [d23, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13736 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (4 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13732 pattern childGuard
    simpa only [d34, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13735 pattern childGuard
    simpa only [d34, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13737 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (4 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10524 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10460 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13738 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (4 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13634 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13737 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13739 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (4 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13636 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13733 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13740 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (4 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13636 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13739 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13741 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (4 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13738 pattern childGuard
    simpa only [d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13740 pattern childGuard
    simpa only [d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13742 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (4 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13736 pattern childGuard
    simpa only [d828, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13741 pattern childGuard
    simpa only [d828, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13743 (pattern : Twelve) (guard : d1 pattern = 1) : d842 pattern ≤ (4 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13642 pattern childGuard
    simpa only [d842, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13742 pattern childGuard
    simpa only [d842, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13744 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (4 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13647 pattern childGuard
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13680 pattern childGuard
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13745 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (4 : Int) + d6 pattern := by
  change (0 : Int) ≤ (4 : Int) + 6
  decide
theorem c13746 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13745 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10494 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13747 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (4 : Int) + d6 pattern := by
  change (1 : Int) ≤ (4 : Int) + 6
  decide
theorem c13748 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13747 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10471 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13749 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13746 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13748 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13750 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13749 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10514 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13751 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13750 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10515 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13752 (pattern : Twelve) (guard : d1 pattern = 1) : d843 pattern ≤ (4 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13744 pattern childGuard
    simpa only [d843, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13751 pattern childGuard
    simpa only [d843, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13753 (pattern : Twelve) (guard : d1 pattern = 1) : d855 pattern ≤ (4 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13743 pattern childGuard
    simpa only [d855, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13752 pattern childGuard
    simpa only [d855, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13754 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (4 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13640 pattern childGuard
    simpa only [d23, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13734 pattern childGuard
    simpa only [d23, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13755 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (4 : Int) + d4 pattern := by
  change (5 : Int) ≤ (4 : Int) + 4
  decide
theorem c13756 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (4 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13666 pattern childGuard
    simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13755 pattern childGuard
    simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13757 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (4 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13667 pattern childGuard
    simpa only [d24, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13756 pattern childGuard
    simpa only [d24, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13758 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (4 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13754 pattern childGuard
    simpa only [d41, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13757 pattern childGuard
    simpa only [d41, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13759 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (4 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13670 pattern childGuard
    simpa only [d815, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13739 pattern childGuard
    simpa only [d815, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13760 (pattern : Twelve) (guard : d1 pattern = 1) : d820 pattern ≤ (4 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13759 pattern childGuard
    simpa only [d820, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d820, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13761 (pattern : Twelve) (guard : d1 pattern = 1) : d829 pattern ≤ (4 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13758 pattern childGuard
    simpa only [d829, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13760 pattern childGuard
    simpa only [d829, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13762 (pattern : Twelve) (guard : d1 pattern = 1) : d844 pattern ≤ (4 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13676 pattern childGuard
    simpa only [d844, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13761 pattern childGuard
    simpa only [d844, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13763 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (4 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13680 pattern childGuard
    simpa only [d40, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d40, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13764 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (4 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13686 pattern childGuard
    simpa only [d830, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13763 pattern childGuard
    simpa only [d830, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13765 (pattern : Twelve) (guard : d1 pattern = 1) : d845 pattern ≤ (4 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13764 pattern childGuard
    simpa only [d845, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10575 pattern childGuard
    simpa only [d845, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13766 (pattern : Twelve) (guard : d1 pattern = 1) : d856 pattern ≤ (4 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13762 pattern childGuard
    simpa only [d856, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13765 pattern childGuard
    simpa only [d856, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13767 (pattern : Twelve) (guard : d1 pattern = 1) : d862 pattern ≤ (4 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13753 pattern childGuard
    simpa only [d862, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13766 pattern childGuard
    simpa only [d862, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13768 (pattern : Twelve) (guard : d0 pattern = 1) : d920 pattern ≤ (4 : Int) + d1313 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13769 (pattern : Twelve) (guard : d1835 pattern = 1) : d928 pattern ≤ (4 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13767 pattern childGuard
    simpa only [d1835, d928, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13768 pattern childGuard
    simpa only [d1835, d928, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13770 (pattern : Twelve) (guard : d2266 pattern = 1) : d933 pattern ≤ (4 : Int) + d1313 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13730 pattern childGuard
    simpa only [d2266, d933, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13769 pattern childGuard
    simpa only [d2266, d933, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13771 (pattern : Twelve) (guard : d0 pattern = 1) : d929 pattern ≤ (4 : Int) + d1316 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13772 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (4 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10524 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13737 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13773 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (4 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13772 pattern childGuard
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13740 pattern childGuard
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13774 (pattern : Twelve) (guard : d1 pattern = 1) : d834 pattern ≤ (4 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13736 pattern childGuard
    simpa only [d834, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13773 pattern childGuard
    simpa only [d834, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13775 (pattern : Twelve) (guard : d1 pattern = 1) : d849 pattern ≤ (4 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13642 pattern childGuard
    simpa only [d849, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13774 pattern childGuard
    simpa only [d849, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13776 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (4 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13647 pattern childGuard
    simpa only [d34, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10626 pattern childGuard
    simpa only [d34, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13777 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (4 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13632 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13650 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13778 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (4 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13677 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13777 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13779 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (4 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13778 pattern childGuard
    simpa only [d38, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13668 pattern childGuard
    simpa only [d38, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13780 (pattern : Twelve) (guard : d1 pattern = 1) : d835 pattern ≤ (4 : Int) + d1283 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13776 pattern childGuard
    simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13779 pattern childGuard
    simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13781 (pattern : Twelve) (guard : d1 pattern = 1) : d850 pattern ≤ (4 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13780 pattern childGuard
    simpa only [d850, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13751 pattern childGuard
    simpa only [d850, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13782 (pattern : Twelve) (guard : d1 pattern = 1) : d859 pattern ≤ (4 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13775 pattern childGuard
    simpa only [d859, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13781 pattern childGuard
    simpa only [d859, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13783 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (4 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13740 pattern childGuard
    simpa only [d47, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d47, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13784 (pattern : Twelve) (guard : d1 pattern = 1) : d836 pattern ≤ (4 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13758 pattern childGuard
    simpa only [d836, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13783 pattern childGuard
    simpa only [d836, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13785 (pattern : Twelve) (guard : d1 pattern = 1) : d851 pattern ≤ (4 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13676 pattern childGuard
    simpa only [d851, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13784 pattern childGuard
    simpa only [d851, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13786 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (4 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13668 pattern childGuard
    simpa only [d48, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d48, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13787 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (4 : Int) + d1290 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13686 pattern childGuard
    simpa only [d837, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13786 pattern childGuard
    simpa only [d837, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13788 (pattern : Twelve) (guard : d1 pattern = 1) : d852 pattern ≤ (4 : Int) + d1302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13787 pattern childGuard
    simpa only [d852, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10575 pattern childGuard
    simpa only [d852, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13789 (pattern : Twelve) (guard : d1 pattern = 1) : d860 pattern ≤ (4 : Int) + d1310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13785 pattern childGuard
    simpa only [d860, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13788 pattern childGuard
    simpa only [d860, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13790 (pattern : Twelve) (guard : d1 pattern = 1) : d865 pattern ≤ (4 : Int) + d1316 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13782 pattern childGuard
    simpa only [d865, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13789 pattern childGuard
    simpa only [d865, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13791 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (4 : Int) + d1316 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13792 (pattern : Twelve) (guard : d1835 pattern = 1) : d930 pattern ≤ (4 : Int) + d1316 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13790 pattern childGuard
    simpa only [d1835, d930, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13791 pattern childGuard
    simpa only [d1835, d930, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13793 (pattern : Twelve) (guard : d2266 pattern = 1) : d934 pattern ≤ (4 : Int) + d1316 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13771 pattern childGuard
    simpa only [d2266, d934, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13792 pattern childGuard
    simpa only [d2266, d934, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13794 (pattern : Twelve) (guard : d2266 pattern = 1) : d936 pattern ≤ (4 : Int) + d2269 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2266 pattern = 1 := by simpa only [d936, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13770 pattern childGuard
    simpa only [d936, d2269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2266 pattern = 1 := by simpa only [d936, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13793 pattern childGuard
    simpa only [d936, d2269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13795 (pattern : Twelve) (guard : d0 pattern = 1) : d931 pattern ≤ (4 : Int) + d1313 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13796 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (4 : Int) + d1313 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13797 (pattern : Twelve) (guard : d1835 pattern = 1) : d932 pattern ≤ (4 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13767 pattern childGuard
    simpa only [d1835, d932, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13796 pattern childGuard
    simpa only [d1835, d932, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13798 (pattern : Twelve) (guard : d2266 pattern = 1) : d935 pattern ≤ (4 : Int) + d1313 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13795 pattern childGuard
    simpa only [d2266, d935, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13797 pattern childGuard
    simpa only [d2266, d935, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13799 (pattern : Twelve) (guard : d2266 pattern = 1) : d937 pattern ≤ (4 : Int) + d2269 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2266 pattern = 1 := by simpa only [d937, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13798 pattern childGuard
    simpa only [d937, d2269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2266 pattern = 1 := by simpa only [d937, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13793 pattern childGuard
    simpa only [d937, d2269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13800 (pattern : Twelve) (guard : d2266 pattern = 1) : d938 pattern ≤ (4 : Int) + d2269 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2266 pattern = 1 := by simpa only [d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13794 pattern childGuard
    simpa only [d938, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2266 pattern = 1 := by simpa only [d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13799 pattern childGuard
    simpa only [d938, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13801 (pattern : Twelve) (guard : d2266 pattern = 1) : d939 pattern ≤ (4 : Int) + d2269 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2266 pattern = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13800 pattern childGuard
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2266 pattern = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13799 pattern childGuard
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13802 (pattern : Twelve) (guard : d0 pattern = 1) : d1368 pattern ≤ (4 : Int) + d1660 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13803 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (4 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10460 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13648 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13804 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (4 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13646 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13803 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13805 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (4 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13733 pattern childGuard
    simpa only [d117, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13681 pattern childGuard
    simpa only [d117, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13806 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (4 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13679 pattern childGuard
    simpa only [d1276, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13805 pattern childGuard
    simpa only [d1276, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13807 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (4 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13804 pattern childGuard
    simpa only [d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13806 pattern childGuard
    simpa only [d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13808 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (4 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10524 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13645 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13809 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (4 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13808 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13803 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13810 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (4 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13636 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13678 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13811 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (4 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13810 pattern childGuard
    simpa only [d119, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13805 pattern childGuard
    simpa only [d119, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13812 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (4 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13809 pattern childGuard
    simpa only [d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13811 pattern childGuard
    simpa only [d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13813 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (4 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13807 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13812 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13814 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (4 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13744 pattern childGuard
    simpa only [d1297, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13813 pattern childGuard
    simpa only [d1297, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13815 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (4 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13657 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10646 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13816 (pattern : Twelve) (guard : d1 pattern = 1) : d1298 pattern ≤ (4 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13815 pattern childGuard
    simpa only [d1298, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d1298, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13817 (pattern : Twelve) (guard : d1 pattern = 1) : d1307 pattern ≤ (4 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13814 pattern childGuard
    simpa only [d1307, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13816 pattern childGuard
    simpa only [d1307, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13818 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (4 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13755 pattern childGuard
    simpa only [d14, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d14, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13819 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (4 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13684 pattern childGuard
    simpa only [d1277, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13818 pattern childGuard
    simpa only [d1277, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13820 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (4 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13806 pattern childGuard
    simpa only [d1282, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13819 pattern childGuard
    simpa only [d1282, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13821 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (4 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13811 pattern childGuard
    simpa only [d125, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d125, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13822 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (4 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13820 pattern childGuard
    simpa only [d1288, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13821 pattern childGuard
    simpa only [d1288, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13823 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (4 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13764 pattern childGuard
    simpa only [d1299, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13822 pattern childGuard
    simpa only [d1299, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13824 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (4 : Int) + d1300 pattern := by
  omega
theorem c13825 (pattern : Twelve) (guard : d1 pattern = 1) : d1308 pattern ≤ (4 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13823 pattern childGuard
    simpa only [d1308, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13824 pattern childGuard
    simpa only [d1308, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13826 (pattern : Twelve) (guard : d1 pattern = 1) : d1314 pattern ≤ (4 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13817 pattern childGuard
    simpa only [d1314, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13825 pattern childGuard
    simpa only [d1314, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13827 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (4 : Int) + d1660 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13828 (pattern : Twelve) (guard : d1835 pattern = 1) : d1369 pattern ≤ (4 : Int) + d1660 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13826 pattern childGuard
    simpa only [d1835, d1369, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13827 pattern childGuard
    simpa only [d1835, d1369, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13829 (pattern : Twelve) (guard : d2266 pattern = 1) : d1373 pattern ≤ (4 : Int) + d1660 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13802 pattern childGuard
    simpa only [d2266, d1373, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13828 pattern childGuard
    simpa only [d2266, d1373, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13830 (pattern : Twelve) (guard : d0 pattern = 1) : d1370 pattern ≤ (4 : Int) + d1660 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13831 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (4 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13653 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13685 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13832 (pattern : Twelve) (guard : d1 pattern = 1) : d1291 pattern ≤ (4 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13815 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13831 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13833 (pattern : Twelve) (guard : d1 pattern = 1) : d1303 pattern ≤ (4 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13832 pattern childGuard
    simpa only [d1303, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d1303, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13834 (pattern : Twelve) (guard : d1 pattern = 1) : d1311 pattern ≤ (4 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13814 pattern childGuard
    simpa only [d1311, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13833 pattern childGuard
    simpa only [d1311, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13835 (pattern : Twelve) (guard : d1 pattern = 1) : d1292 pattern ≤ (4 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10645 pattern childGuard
    simpa only [d1292, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13714 pattern childGuard
    simpa only [d1292, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13836 (pattern : Twelve) (guard : d1 pattern = 1) : d1304 pattern ≤ (4 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13835 pattern childGuard
    simpa only [d1304, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d1304, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13837 (pattern : Twelve) (guard : d1 pattern = 1) : d1312 pattern ≤ (4 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13823 pattern childGuard
    simpa only [d1312, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13836 pattern childGuard
    simpa only [d1312, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13838 (pattern : Twelve) (guard : d1 pattern = 1) : d1317 pattern ≤ (4 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13834 pattern childGuard
    simpa only [d1317, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13837 pattern childGuard
    simpa only [d1317, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13839 (pattern : Twelve) (guard : d1835 pattern = 1) : d1371 pattern ≤ (4 : Int) + d1660 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13838 pattern childGuard
    simpa only [d1835, d1371, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13827 pattern childGuard
    simpa only [d1835, d1371, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13840 (pattern : Twelve) (guard : d2266 pattern = 1) : d1374 pattern ≤ (4 : Int) + d1660 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13830 pattern childGuard
    simpa only [d2266, d1374, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13839 pattern childGuard
    simpa only [d2266, d1374, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13841 (pattern : Twelve) (guard : d2266 pattern = 1) : d1376 pattern ≤ (4 : Int) + d1660 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2266 pattern = 1 := by simpa only [d1376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13829 pattern childGuard
    simpa only [d1376, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2266 pattern = 1 := by simpa only [d1376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13840 pattern childGuard
    simpa only [d1376, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13842 (pattern : Twelve) (guard : d0 pattern = 1) : d1372 pattern ≤ (4 : Int) + d1660 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13843 (pattern : Twelve) (guard : d2266 pattern = 1) : d1375 pattern ≤ (4 : Int) + d1660 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d1375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13842 pattern childGuard
    simpa only [d2266, d1375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d1375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13828 pattern childGuard
    simpa only [d2266, d1375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13844 (pattern : Twelve) (guard : d2266 pattern = 1) : d1377 pattern ≤ (4 : Int) + d1660 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2266 pattern = 1 := by simpa only [d1377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13843 pattern childGuard
    simpa only [d1377, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2266 pattern = 1 := by simpa only [d1377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13840 pattern childGuard
    simpa only [d1377, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13845 (pattern : Twelve) (guard : d2266 pattern = 1) : d1378 pattern ≤ (4 : Int) + d1660 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2266 pattern = 1 := by simpa only [d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13841 pattern childGuard
    simpa only [d1378, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2266 pattern = 1 := by simpa only [d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13844 pattern childGuard
    simpa only [d1378, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13846 (pattern : Twelve) (guard : d2266 pattern = 1) : d1379 pattern ≤ (4 : Int) + d1660 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2266 pattern = 1 := by simpa only [d1379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13845 pattern childGuard
    simpa only [d1379, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2266 pattern = 1 := by simpa only [d1379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13844 pattern childGuard
    simpa only [d1379, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13847 (pattern : Twelve) (guard : d0 pattern = 1) : d1686 pattern ≤ (4 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13848 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13748 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10513 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13849 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13848 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10477 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13850 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13750 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13849 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13851 (pattern : Twelve) (guard : d1 pattern = 1) : d1653 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10573 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13852 (pattern : Twelve) (guard : d1 pattern = 1) : d1658 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13850 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13851 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13853 (pattern : Twelve) (guard : d1 pattern = 1) : d1661 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13852 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10656 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13854 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (4 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13855 (pattern : Twelve) (guard : d1835 pattern = 1) : d1687 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13853 pattern childGuard
    simpa only [d1835, d1687, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13854 pattern childGuard
    simpa only [d1835, d1687, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13856 (pattern : Twelve) (guard : d2266 pattern = 1) : d1688 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2266, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13847 pattern childGuard
    simpa only [d2266, d1688, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d2266, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13855 pattern childGuard
    simpa only [d2266, d1688, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13857 (pattern : Twelve) (guard : d0 pattern = 1) : d358 pattern ≤ (0 : Int) + d110 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13858 (pattern : Twelve) (guard : d0 pattern = 1) : d211 pattern ≤ (0 : Int) + d92 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13859 (pattern : Twelve) (guard : d1844 pattern = 1) : d354 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d354, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c732 pattern childGuard
    simpa only [d1844, d354, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d354, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13858 pattern childGuard
    simpa only [d1844, d354, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
