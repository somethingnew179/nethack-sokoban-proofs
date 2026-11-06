/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons04
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c800 (pattern : Ten) (guard : d372 pattern = 1) : d280 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d372, d280, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d372, d280, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d372, d280, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c799 pattern childGuard
    simpa only [d372, d280, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c801 (pattern : Ten) (guard : d0 pattern = 1) : d202 pattern ≤ (0 : Int) + d203 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c802 (pattern : Ten) (guard : d372 pattern = 1) : d202 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d372, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d372, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d372, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c801 pattern childGuard
    simpa only [d372, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c803 (pattern : Ten) (guard : d372 pattern = 1) : d281 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c800 pattern childGuard
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d372 pattern = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c802 pattern childGuard
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c804 (pattern : Ten) (guard : d372 pattern = 1) : d284 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c803 pattern childGuard
    simpa only [d284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d372 pattern = 1 := by simpa only [d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c802 pattern childGuard
    simpa only [d284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c805 (pattern : Ten) (guard : d372 pattern = 1) : d282 pattern ≤ (0 : Int) + d211 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d282, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c802 pattern childGuard
    simpa only [d282, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d372 pattern = 1 := by simpa only [d282, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c250 pattern childGuard
    simpa only [d282, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c806 (pattern : Ten) (guard : d0 pattern = 1) : d204 pattern ≤ (0 : Int) + d205 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c807 (pattern : Ten) (guard : d372 pattern = 1) : d204 pattern ≤ (0 : Int) + d208 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d372, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c252 pattern childGuard
    simpa only [d372, d208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d372, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c806 pattern childGuard
    simpa only [d372, d208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c808 (pattern : Ten) (guard : d372 pattern = 1) : d283 pattern ≤ (0 : Int) + d212 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d283, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c807 pattern childGuard
    simpa only [d283, d212, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d372 pattern = 1 := by simpa only [d283, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c250 pattern childGuard
    simpa only [d283, d212, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c809 (pattern : Ten) (guard : d372 pattern = 1) : d285 pattern ≤ (0 : Int) + d215 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d285, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c805 pattern childGuard
    simpa only [d285, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d372 pattern = 1 := by simpa only [d285, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c808 pattern childGuard
    simpa only [d285, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c810 (pattern : Ten) (guard : d372 pattern = 1) : d286 pattern ≤ (0 : Int) + d218 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d286, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c804 pattern childGuard
    simpa only [d286, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d372 pattern = 1 := by simpa only [d286, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c809 pattern childGuard
    simpa only [d286, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c811 (pattern : Ten) (guard : d0 pattern = 1) : d287 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c812 (pattern : Ten) (guard : d375 pattern = 1) : d288 pattern ≤ (0 : Int) + d289 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d375, d288, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c810 pattern childGuard
    simpa only [d375, d288, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d375, d288, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c811 pattern childGuard
    simpa only [d375, d288, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c813 (pattern : Ten) (guard : d0 pattern = 1) : d42 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c814 (pattern : Ten) (guard : d389 pattern = 1) : d48 pattern ≤ (0 : Int) + d108 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d389, d48, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c627 pattern childGuard
    simpa only [d389, d48, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d389, d48, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c813 pattern childGuard
    simpa only [d389, d48, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c815 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d15 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c816 (pattern : Ten) (guard : d390 pattern = 1) : d124 pattern ≤ (0 : Int) + d109 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d389 pattern = 1 := by simpa only [d390, d124, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c814 pattern childGuard
    simpa only [d390, d124, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d390, d124, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c815 pattern childGuard
    simpa only [d390, d124, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c817 (pattern : Ten) (guard : d0 pattern = 1) : d42 pattern ≤ (0 : Int) + d15 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c818 (pattern : Ten) (guard : d389 pattern = 1) : d48 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d389, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c627 pattern childGuard
    simpa only [d389, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d389, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c817 pattern childGuard
    simpa only [d389, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c819 (pattern : Ten) (guard : d0 pattern = 1) : d48 pattern ≤ (0 : Int) + d14 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c820 (pattern : Ten) (guard : d390 pattern = 1) : d48 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d389 pattern = 1 := by simpa only [d390, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c818 pattern childGuard
    simpa only [d390, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d390, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c819 pattern childGuard
    simpa only [d390, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c821 (pattern : Ten) (guard : d390 pattern = 1) : d125 pattern ≤ (0 : Int) + d115 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d125, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c816 pattern childGuard
    simpa only [d125, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d125, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c820 pattern childGuard
    simpa only [d125, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c822 (pattern : Ten) (guard : d0 pattern = 1) : d48 pattern ≤ (0 : Int) + d44 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c823 (pattern : Ten) (guard : d390 pattern = 1) : d48 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d389 pattern = 1 := by simpa only [d390, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c818 pattern childGuard
    simpa only [d390, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d390, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c822 pattern childGuard
    simpa only [d390, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c824 (pattern : Ten) (guard : d390 pattern = 1) : d48 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c823 pattern childGuard
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c820 pattern childGuard
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c825 (pattern : Ten) (guard : d390 pattern = 1) : d128 pattern ≤ (0 : Int) + d119 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d128, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c821 pattern childGuard
    simpa only [d128, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d128, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c824 pattern childGuard
    simpa only [d128, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c826 (pattern : Ten) (guard : d0 pattern = 1) : d48 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c827 (pattern : Ten) (guard : d390 pattern = 1) : d48 pattern ≤ (0 : Int) + d112 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d389 pattern = 1 := by simpa only [d390, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c818 pattern childGuard
    simpa only [d390, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d390, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c826 pattern childGuard
    simpa only [d390, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c828 (pattern : Ten) (guard : d389 pattern = 1) : d20 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d389, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c643 pattern childGuard
    simpa only [d389, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d389, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c511 pattern childGuard
    simpa only [d389, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c829 (pattern : Ten) (guard : d390 pattern = 1) : d20 pattern ≤ (0 : Int) + d113 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d389 pattern = 1 := by simpa only [d390, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c828 pattern childGuard
    simpa only [d390, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d390, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c789 pattern childGuard
    simpa only [d390, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c830 (pattern : Ten) (guard : d390 pattern = 1) : d126 pattern ≤ (0 : Int) + d117 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d126, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c827 pattern childGuard
    simpa only [d126, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d126, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c829 pattern childGuard
    simpa only [d126, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c831 (pattern : Ten) (guard : d0 pattern = 1) : d43 pattern ≤ (0 : Int) + d44 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c832 (pattern : Ten) (guard : d389 pattern = 1) : d50 pattern ≤ (0 : Int) + d44 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d389, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c648 pattern childGuard
    simpa only [d389, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d389, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c831 pattern childGuard
    simpa only [d389, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c833 (pattern : Ten) (guard : d0 pattern = 1) : d50 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c834 (pattern : Ten) (guard : d390 pattern = 1) : d50 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d389 pattern = 1 := by simpa only [d390, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c832 pattern childGuard
    simpa only [d390, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d390, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c833 pattern childGuard
    simpa only [d390, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c835 (pattern : Ten) (guard : d390 pattern = 1) : d127 pattern ≤ (0 : Int) + d118 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d127, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c834 pattern childGuard
    simpa only [d127, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d127, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c829 pattern childGuard
    simpa only [d127, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c836 (pattern : Ten) (guard : d390 pattern = 1) : d129 pattern ≤ (0 : Int) + d120 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d129, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c830 pattern childGuard
    simpa only [d129, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d129, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c835 pattern childGuard
    simpa only [d129, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c837 (pattern : Ten) (guard : d390 pattern = 1) : d130 pattern ≤ (0 : Int) + d121 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d130, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c825 pattern childGuard
    simpa only [d130, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d130, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c836 pattern childGuard
    simpa only [d130, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c838 (pattern : Ten) (guard : d390 pattern = 1) : d131 pattern ≤ (0 : Int) + d122 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d131, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c836 pattern childGuard
    simpa only [d131, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d131, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c656 pattern childGuard
    simpa only [d131, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c839 (pattern : Ten) (guard : d390 pattern = 1) : d132 pattern ≤ (0 : Int) + d123 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d132, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c837 pattern childGuard
    simpa only [d132, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d132, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c838 pattern childGuard
    simpa only [d132, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c840 (pattern : Ten) (guard : d0 pattern = 1) : d197 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c841 (pattern : Ten) (guard : d386 pattern = 1) : d202 pattern ≤ (0 : Int) + d266 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d386, d202, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c659 pattern childGuard
    simpa only [d386, d202, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d386, d202, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c840 pattern childGuard
    simpa only [d386, d202, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c842 (pattern : Ten) (guard : d391 pattern = 1) : d280 pattern ≤ (0 : Int) + d267 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d386 pattern = 1 := by simpa only [d391, d280, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c841 pattern childGuard
    simpa only [d391, d280, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d391, d280, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c538 pattern childGuard
    simpa only [d391, d280, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c843 (pattern : Ten) (guard : d0 pattern = 1) : d197 pattern ≤ (0 : Int) + d174 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c844 (pattern : Ten) (guard : d386 pattern = 1) : d202 pattern ≤ (0 : Int) + d174 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d386, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c659 pattern childGuard
    simpa only [d386, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d386, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c843 pattern childGuard
    simpa only [d386, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c845 (pattern : Ten) (guard : d0 pattern = 1) : d202 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c846 (pattern : Ten) (guard : d391 pattern = 1) : d202 pattern ≤ (0 : Int) + d268 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d386 pattern = 1 := by simpa only [d391, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c844 pattern childGuard
    simpa only [d391, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d391, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c845 pattern childGuard
    simpa only [d391, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c847 (pattern : Ten) (guard : d391 pattern = 1) : d281 pattern ≤ (0 : Int) + d271 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d281, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c842 pattern childGuard
    simpa only [d281, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d281, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c846 pattern childGuard
    simpa only [d281, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c848 (pattern : Ten) (guard : d0 pattern = 1) : d202 pattern ≤ (0 : Int) + d199 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c849 (pattern : Ten) (guard : d391 pattern = 1) : d202 pattern ≤ (0 : Int) + d269 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d386 pattern = 1 := by simpa only [d391, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c844 pattern childGuard
    simpa only [d391, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d391, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c848 pattern childGuard
    simpa only [d391, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c850 (pattern : Ten) (guard : d391 pattern = 1) : d202 pattern ≤ (0 : Int) + d272 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c849 pattern childGuard
    simpa only [d272, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c846 pattern childGuard
    simpa only [d272, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c851 (pattern : Ten) (guard : d391 pattern = 1) : d284 pattern ≤ (0 : Int) + d275 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d284, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c847 pattern childGuard
    simpa only [d284, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d284, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c850 pattern childGuard
    simpa only [d284, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c852 (pattern : Ten) (guard : d391 pattern = 1) : d282 pattern ≤ (0 : Int) + d273 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d282, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c846 pattern childGuard
    simpa only [d282, d273, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d282, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c673 pattern childGuard
    simpa only [d282, d273, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c853 (pattern : Ten) (guard : d0 pattern = 1) : d198 pattern ≤ (0 : Int) + d199 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c854 (pattern : Ten) (guard : d386 pattern = 1) : d204 pattern ≤ (0 : Int) + d199 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d386, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c675 pattern childGuard
    simpa only [d386, d204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d386, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c853 pattern childGuard
    simpa only [d386, d204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c855 (pattern : Ten) (guard : d0 pattern = 1) : d204 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c856 (pattern : Ten) (guard : d391 pattern = 1) : d204 pattern ≤ (0 : Int) + d270 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d386 pattern = 1 := by simpa only [d391, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c854 pattern childGuard
    simpa only [d391, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d391, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c855 pattern childGuard
    simpa only [d391, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c857 (pattern : Ten) (guard : d391 pattern = 1) : d283 pattern ≤ (0 : Int) + d274 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d283, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c856 pattern childGuard
    simpa only [d283, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d283, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c673 pattern childGuard
    simpa only [d283, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c858 (pattern : Ten) (guard : d391 pattern = 1) : d285 pattern ≤ (0 : Int) + d276 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d285, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c852 pattern childGuard
    simpa only [d285, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d285, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c857 pattern childGuard
    simpa only [d285, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c859 (pattern : Ten) (guard : d391 pattern = 1) : d286 pattern ≤ (0 : Int) + d277 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d286, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c851 pattern childGuard
    simpa only [d286, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d286, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c858 pattern childGuard
    simpa only [d286, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c860 (pattern : Ten) (guard : d391 pattern = 1) : d287 pattern ≤ (0 : Int) + d278 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d287, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c858 pattern childGuard
    simpa only [d287, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d287, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c673 pattern childGuard
    simpa only [d287, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c861 (pattern : Ten) (guard : d391 pattern = 1) : d288 pattern ≤ (0 : Int) + d279 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d288, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c859 pattern childGuard
    simpa only [d288, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d288, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c860 pattern childGuard
    simpa only [d288, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c862 (pattern : Ten) (guard : d0 pattern = 1) : d131 pattern ≤ (0 : Int) + d65 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c863 (pattern : Ten) (guard : d374 pattern = 1) : d132 pattern ≤ (0 : Int) + d66 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d374, d132, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c796 pattern childGuard
    simpa only [d374, d132, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d374, d132, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c862 pattern childGuard
    simpa only [d374, d132, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c864 (pattern : Ten) (guard : d0 pattern = 1) : d287 pattern ≤ (0 : Int) + d219 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c865 (pattern : Ten) (guard : d375 pattern = 1) : d288 pattern ≤ (0 : Int) + d220 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d375, d288, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c810 pattern childGuard
    simpa only [d375, d288, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d375, d288, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c864 pattern childGuard
    simpa only [d375, d288, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c866 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d65 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c867 (pattern : Ten) (guard : d362 pattern = 1) : d133 pattern ≤ (0 : Int) + d66 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d362, d133, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c208 pattern childGuard
    simpa only [d362, d133, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d362, d133, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c866 pattern childGuard
    simpa only [d362, d133, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c868 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d219 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c869 (pattern : Ten) (guard : d361 pattern = 1) : d289 pattern ≤ (0 : Int) + d220 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d361, d289, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c211 pattern childGuard
    simpa only [d361, d289, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d361, d289, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c868 pattern childGuard
    simpa only [d361, d289, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c870 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c871 (pattern : Ten) (guard : d392 pattern = 1) : d133 pattern ≤ (0 : Int) + d135 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d367 pattern = 1 := by simpa only [d392, d133, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c215 pattern childGuard
    simpa only [d392, d133, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d392, d133, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c870 pattern childGuard
    simpa only [d392, d133, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c872 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c873 (pattern : Ten) (guard : d393 pattern = 1) : d289 pattern ≤ (0 : Int) + d291 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d366 pattern = 1 := by simpa only [d393, d289, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c220 pattern childGuard
    simpa only [d393, d289, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d393, d289, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c872 pattern childGuard
    simpa only [d393, d289, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c874 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d131 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c875 (pattern : Ten) (guard : d374 pattern = 1) : d133 pattern ≤ (0 : Int) + d132 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d374, d133, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d374, d133, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d374, d133, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c874 pattern childGuard
    simpa only [d374, d133, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c876 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c877 (pattern : Ten) (guard : d375 pattern = 1) : d289 pattern ≤ (0 : Int) + d288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d375, d289, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c257 pattern childGuard
    simpa only [d375, d289, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d375, d289, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c876 pattern childGuard
    simpa only [d375, d289, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c878 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d84 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c879 (pattern : Ten) (guard : d377 pattern = 1) : d133 pattern ≤ (0 : Int) + d85 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d377, d133, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c67 pattern childGuard
    simpa only [d377, d133, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d377, d133, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c878 pattern childGuard
    simpa only [d377, d133, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c880 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d237 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c881 (pattern : Ten) (guard : d378 pattern = 1) : d289 pattern ≤ (0 : Int) + d238 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d353 pattern = 1 := by simpa only [d378, d289, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c80 pattern childGuard
    simpa only [d378, d289, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d378, d289, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c880 pattern childGuard
    simpa only [d378, d289, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c882 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c883 (pattern : Ten) (guard : d395 pattern = 1) : d54 pattern ≤ (0 : Int) + d150 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d395, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c882 pattern childGuard
    simpa only [d395, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c884 (pattern : Ten) (guard : d395 pattern = 1) : d54 pattern ≤ (0 : Int) + d54 pattern := by
  omega
theorem c885 (pattern : Ten) (guard : d395 pattern = 1) : d54 pattern ≤ (0 : Int) + d151 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c883 pattern childGuard
    simpa only [d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c884 pattern childGuard
    simpa only [d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c886 (pattern : Ten) (guard : d0 pattern = 1) : d62 pattern ≤ (0 : Int) + d152 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c887 (pattern : Ten) (guard : d397 pattern = 1) : d64 pattern ≤ (0 : Int) + d154 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d397, d64, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c885 pattern childGuard
    simpa only [d397, d64, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d397, d64, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c886 pattern childGuard
    simpa only [d397, d64, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c888 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d155 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c889 (pattern : Ten) (guard : d398 pattern = 1) : d133 pattern ≤ (0 : Int) + d156 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d397 pattern = 1 := by simpa only [d398, d133, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c887 pattern childGuard
    simpa only [d398, d133, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d398, d133, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c888 pattern childGuard
    simpa only [d398, d133, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c890 (pattern : Ten) (guard : d394 pattern = 1) : d207 pattern ≤ (0 : Int) + d211 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d394, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c75 pattern childGuard
    simpa only [d394, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c891 (pattern : Ten) (guard : d394 pattern = 1) : d207 pattern ≤ (0 : Int) + d207 pattern := by
  omega
theorem c892 (pattern : Ten) (guard : d394 pattern = 1) : d207 pattern ≤ (0 : Int) + d326 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c890 pattern childGuard
    simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c891 pattern childGuard
    simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c893 (pattern : Ten) (guard : d0 pattern = 1) : d215 pattern ≤ (0 : Int) + d327 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c894 (pattern : Ten) (guard : d400 pattern = 1) : d218 pattern ≤ (0 : Int) + d329 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d400, d218, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c892 pattern childGuard
    simpa only [d400, d218, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d400, d218, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c893 pattern childGuard
    simpa only [d400, d218, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c895 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d330 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c896 (pattern : Ten) (guard : d401 pattern = 1) : d289 pattern ≤ (0 : Int) + d331 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d400 pattern = 1 := by simpa only [d401, d289, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c894 pattern childGuard
    simpa only [d401, d289, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d401, d289, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c895 pattern childGuard
    simpa only [d401, d289, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c897 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (0 : Int) + d58 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c898 (pattern : Ten) (guard : d368 pattern = 1) : d134 pattern ≤ (0 : Int) + d83 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d368, d134, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c63 pattern childGuard
    simpa only [d368, d134, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d368, d134, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c897 pattern childGuard
    simpa only [d368, d134, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c899 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (0 : Int) + d60 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c900 (pattern : Ten) (guard : d368 pattern = 1) : d56 pattern ≤ (0 : Int) + d84 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d368, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c68 pattern childGuard
    simpa only [d368, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d368, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c899 pattern childGuard
    simpa only [d368, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c901 (pattern : Ten) (guard : d368 pattern = 1) : d135 pattern ≤ (0 : Int) + d85 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d368 pattern = 1 := by simpa only [d135, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c898 pattern childGuard
    simpa only [d135, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d368 pattern = 1 := by simpa only [d135, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c900 pattern childGuard
    simpa only [d135, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c902 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d211 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c903 (pattern : Ten) (guard : d370 pattern = 1) : d290 pattern ≤ (0 : Int) + d236 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d353 pattern = 1 := by simpa only [d370, d290, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c76 pattern childGuard
    simpa only [d370, d290, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d370, d290, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c902 pattern childGuard
    simpa only [d370, d290, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c904 (pattern : Ten) (guard : d0 pattern = 1) : d209 pattern ≤ (0 : Int) + d214 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c905 (pattern : Ten) (guard : d370 pattern = 1) : d209 pattern ≤ (0 : Int) + d237 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d353 pattern = 1 := by simpa only [d370, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c287 pattern childGuard
    simpa only [d370, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d370, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c904 pattern childGuard
    simpa only [d370, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c906 (pattern : Ten) (guard : d370 pattern = 1) : d291 pattern ≤ (0 : Int) + d238 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d370 pattern = 1 := by simpa only [d291, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c903 pattern childGuard
    simpa only [d291, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d370 pattern = 1 := by simpa only [d291, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c905 pattern childGuard
    simpa only [d291, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c907 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (0 : Int) + d62 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c908 (pattern : Ten) (guard : d367 pattern = 1) : d134 pattern ≤ (0 : Int) + d64 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d367, d134, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d367, d134, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d367, d134, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c907 pattern childGuard
    simpa only [d367, d134, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c909 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (0 : Int) + d63 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c910 (pattern : Ten) (guard : d367 pattern = 1) : d56 pattern ≤ (0 : Int) + d65 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d367, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c331 pattern childGuard
    simpa only [d367, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d367, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c909 pattern childGuard
    simpa only [d367, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c911 (pattern : Ten) (guard : d367 pattern = 1) : d135 pattern ≤ (0 : Int) + d66 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d367 pattern = 1 := by simpa only [d135, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c908 pattern childGuard
    simpa only [d135, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d367 pattern = 1 := by simpa only [d135, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c910 pattern childGuard
    simpa only [d135, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c912 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d215 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c913 (pattern : Ten) (guard : d367 pattern = 1) : d290 pattern ≤ (0 : Int) + d298 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d367, d290, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c315 pattern childGuard
    simpa only [d367, d290, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d367, d290, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c912 pattern childGuard
    simpa only [d367, d290, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c914 (pattern : Ten) (guard : d0 pattern = 1) : d209 pattern ≤ (0 : Int) + d217 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c915 (pattern : Ten) (guard : d367 pattern = 1) : d209 pattern ≤ (0 : Int) + d299 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d367, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c318 pattern childGuard
    simpa only [d367, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d367, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c914 pattern childGuard
    simpa only [d367, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c916 (pattern : Ten) (guard : d367 pattern = 1) : d291 pattern ≤ (0 : Int) + d300 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d367 pattern = 1 := by simpa only [d291, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c913 pattern childGuard
    simpa only [d291, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d367 pattern = 1 := by simpa only [d291, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c915 pattern childGuard
    simpa only [d291, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c917 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (0 : Int) + d152 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c918 (pattern : Ten) (guard : d397 pattern = 1) : d134 pattern ≤ (0 : Int) + d154 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d397, d134, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c885 pattern childGuard
    simpa only [d397, d134, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d397, d134, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c917 pattern childGuard
    simpa only [d397, d134, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c919 (pattern : Ten) (guard : d395 pattern = 1) : d56 pattern ≤ (0 : Int) + d56 pattern := by
  omega
theorem c920 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (0 : Int) + d153 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c921 (pattern : Ten) (guard : d397 pattern = 1) : d56 pattern ≤ (0 : Int) + d155 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d397, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c919 pattern childGuard
    simpa only [d397, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d397, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c920 pattern childGuard
    simpa only [d397, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c922 (pattern : Ten) (guard : d397 pattern = 1) : d135 pattern ≤ (0 : Int) + d156 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d397 pattern = 1 := by simpa only [d135, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c918 pattern childGuard
    simpa only [d135, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d397 pattern = 1 := by simpa only [d135, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c921 pattern childGuard
    simpa only [d135, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c923 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d327 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c924 (pattern : Ten) (guard : d400 pattern = 1) : d290 pattern ≤ (0 : Int) + d329 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d400, d290, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c892 pattern childGuard
    simpa only [d400, d290, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d400, d290, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c923 pattern childGuard
    simpa only [d400, d290, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c925 (pattern : Ten) (guard : d394 pattern = 1) : d209 pattern ≤ (0 : Int) + d209 pattern := by
  omega
theorem c926 (pattern : Ten) (guard : d0 pattern = 1) : d209 pattern ≤ (0 : Int) + d328 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c927 (pattern : Ten) (guard : d400 pattern = 1) : d209 pattern ≤ (0 : Int) + d330 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d400, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c925 pattern childGuard
    simpa only [d400, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d400, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c926 pattern childGuard
    simpa only [d400, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c928 (pattern : Ten) (guard : d400 pattern = 1) : d291 pattern ≤ (0 : Int) + d331 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d400 pattern = 1 := by simpa only [d291, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c924 pattern childGuard
    simpa only [d291, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d400 pattern = 1 := by simpa only [d291, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c927 pattern childGuard
    simpa only [d291, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c929 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c930 (pattern : Ten) (guard : d392 pattern = 1) : d135 pattern ≤ (0 : Int) + d133 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d367 pattern = 1 := by simpa only [d392, d135, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c908 pattern childGuard
    simpa only [d392, d135, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d392, d135, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c929 pattern childGuard
    simpa only [d392, d135, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c931 (pattern : Ten) (guard : d366 pattern = 1) : d290 pattern ≤ (0 : Int) + d218 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d366, d290, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d366, d290, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d366, d290, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c912 pattern childGuard
    simpa only [d366, d290, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c932 (pattern : Ten) (guard : d0 pattern = 1) : d209 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c933 (pattern : Ten) (guard : d393 pattern = 1) : d291 pattern ≤ (0 : Int) + d289 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d366 pattern = 1 := by simpa only [d393, d291, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c931 pattern childGuard
    simpa only [d393, d291, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d393, d291, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c932 pattern childGuard
    simpa only [d393, d291, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c934 (pattern : Ten) (guard : d382 pattern = 1) : d290 pattern ≤ (0 : Int) + d218 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d381 pattern = 1 := by simpa only [d382, d290, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c334 pattern childGuard
    simpa only [d382, d290, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d382, d290, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c912 pattern childGuard
    simpa only [d382, d290, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c935 (pattern : Ten) (guard : d0 pattern = 1) : d195 pattern ≤ (0 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c936 (pattern : Ten) (guard : d350 pattern = 1) : d195 pattern ≤ (0 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c319 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c935 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c937 (pattern : Ten) (guard : d350 pattern = 1) : d200 pattern ≤ (0 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d200, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c936 pattern childGuard
    simpa only [d200, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d200, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d200, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c938 (pattern : Ten) (guard : d350 pattern = 1) : d205 pattern ≤ (0 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d205, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c937 pattern childGuard
    simpa only [d205, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d205, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d205, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c939 (pattern : Ten) (guard : d350 pattern = 1) : d209 pattern ≤ (0 : Int) + d210 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d209, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c938 pattern childGuard
    simpa only [d209, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d209, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d209, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c940 (pattern : Ten) (guard : d350 pattern = 1) : d209 pattern ≤ (0 : Int) + d213 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c318 pattern childGuard
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c939 pattern childGuard
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c941 (pattern : Ten) (guard : d381 pattern = 1) : d209 pattern ≤ (0 : Int) + d216 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d381, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d381, d216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d381, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c940 pattern childGuard
    simpa only [d381, d216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c942 (pattern : Ten) (guard : d382 pattern = 1) : d209 pattern ≤ (0 : Int) + d219 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d381 pattern = 1 := by simpa only [d382, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c941 pattern childGuard
    simpa only [d382, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d382, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c914 pattern childGuard
    simpa only [d382, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c943 (pattern : Ten) (guard : d382 pattern = 1) : d291 pattern ≤ (0 : Int) + d220 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d382 pattern = 1 := by simpa only [d291, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c934 pattern childGuard
    simpa only [d291, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d382 pattern = 1 := by simpa only [d291, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c942 pattern childGuard
    simpa only [d291, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c944 (pattern : Ten) (guard : d0 pattern = 1) : d171 pattern ≤ (0 : Int) + d309 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c945 (pattern : Ten) (guard : d350 pattern = 1) : d171 pattern ≤ (0 : Int) + d313 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c291 pattern childGuard
    simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c944 pattern childGuard
    simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c946 (pattern : Ten) (guard : d0 pattern = 1) : d172 pattern ≤ (0 : Int) + d310 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c947 (pattern : Ten) (guard : d350 pattern = 1) : d172 pattern ≤ (0 : Int) + d314 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c441 pattern childGuard
    simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c946 pattern childGuard
    simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c948 (pattern : Ten) (guard : d350 pattern = 1) : d174 pattern ≤ (0 : Int) + d317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d174, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c945 pattern childGuard
    simpa only [d174, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d174, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c947 pattern childGuard
    simpa only [d174, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c949 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (0 : Int) + d193 pattern := by
  omega
theorem c950 (pattern : Ten) (guard : d0 pattern = 1) : d193 pattern ≤ (0 : Int) + d311 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c951 (pattern : Ten) (guard : d350 pattern = 1) : d193 pattern ≤ (0 : Int) + d315 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c949 pattern childGuard
    simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c950 pattern childGuard
    simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c952 (pattern : Ten) (guard : d350 pattern = 1) : d197 pattern ≤ (0 : Int) + d318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d197, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c951 pattern childGuard
    simpa only [d197, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d197, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d197, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c953 (pattern : Ten) (guard : d350 pattern = 1) : d202 pattern ≤ (0 : Int) + d321 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d202, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c948 pattern childGuard
    simpa only [d202, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d202, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c952 pattern childGuard
    simpa only [d202, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c954 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (0 : Int) + d194 pattern := by
  omega
theorem c955 (pattern : Ten) (guard : d0 pattern = 1) : d194 pattern ≤ (0 : Int) + d312 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c956 (pattern : Ten) (guard : d350 pattern = 1) : d194 pattern ≤ (0 : Int) + d316 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c954 pattern childGuard
    simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c955 pattern childGuard
    simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c957 (pattern : Ten) (guard : d350 pattern = 1) : d198 pattern ≤ (0 : Int) + d319 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d198, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c956 pattern childGuard
    simpa only [d198, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d198, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d198, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c958 (pattern : Ten) (guard : d350 pattern = 1) : d203 pattern ≤ (0 : Int) + d322 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d203, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c957 pattern childGuard
    simpa only [d203, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d203, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d203, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c959 (pattern : Ten) (guard : d350 pattern = 1) : d207 pattern ≤ (0 : Int) + d324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d207, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c953 pattern childGuard
    simpa only [d207, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d207, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c958 pattern childGuard
    simpa only [d207, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
