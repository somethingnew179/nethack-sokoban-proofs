/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons154
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c21700 (pattern : Twelve) (guard : d1 pattern = 1) : d145 pattern ≤ (18 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d145, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21698 pattern childGuard
    simpa only [d145, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d145, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21699 pattern childGuard
    simpa only [d145, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21701 (pattern : Twelve) (guard : d1 pattern = 1) : d149 pattern ≤ (18 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d149, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21695 pattern childGuard
    simpa only [d149, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d149, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21700 pattern childGuard
    simpa only [d149, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21702 (pattern : Twelve) (guard : d1 pattern = 1) : d139 pattern ≤ (18 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d139, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21599 pattern childGuard
    simpa only [d139, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d139, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21697 pattern childGuard
    simpa only [d139, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21703 (pattern : Twelve) (guard : d1 pattern = 1) : d146 pattern ≤ (18 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d146, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21702 pattern childGuard
    simpa only [d146, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d146, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21699 pattern childGuard
    simpa only [d146, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21704 (pattern : Twelve) (guard : d1 pattern = 1) : d150 pattern ≤ (18 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d150, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21695 pattern childGuard
    simpa only [d150, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d150, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21703 pattern childGuard
    simpa only [d150, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21705 (pattern : Twelve) (guard : d1 pattern = 1) : d153 pattern ≤ (18 : Int) + d902 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21701 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21704 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21706 (pattern : Twelve) (guard : d1 pattern = 1) : d122 pattern ≤ (18 : Int) + d878 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d122, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21544 pattern childGuard
    simpa only [d122, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d122, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21619 pattern childGuard
    simpa only [d122, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21707 (pattern : Twelve) (guard : d1 pattern = 1) : d131 pattern ≤ (18 : Int) + d885 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d131, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21696 pattern childGuard
    simpa only [d131, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d131, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21706 pattern childGuard
    simpa only [d131, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21708 (pattern : Twelve) (guard : d1 pattern = 1) : d140 pattern ≤ (18 : Int) + d894 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d140, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21569 pattern childGuard
    simpa only [d140, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d140, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21707 pattern childGuard
    simpa only [d140, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21709 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (18 : Int) + d4 pattern := by
  change (3 : Int) ≤ (18 : Int) + 4
  decide
theorem c21710 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (18 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21609 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21709 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21711 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (18 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21609 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21710 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21712 (pattern : Twelve) (guard : d1 pattern = 1) : d123 pattern ≤ (18 : Int) + d879 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d123, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21540 pattern childGuard
    simpa only [d123, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d123, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21711 pattern childGuard
    simpa only [d123, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21713 (pattern : Twelve) (guard : d1 pattern = 1) : d132 pattern ≤ (18 : Int) + d886 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21581 pattern childGuard
    simpa only [d132, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21712 pattern childGuard
    simpa only [d132, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21714 (pattern : Twelve) (guard : d1 pattern = 1) : d141 pattern ≤ (18 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d141, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21713 pattern childGuard
    simpa only [d141, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d141, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21693 pattern childGuard
    simpa only [d141, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21715 (pattern : Twelve) (guard : d1 pattern = 1) : d147 pattern ≤ (18 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d147, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21708 pattern childGuard
    simpa only [d147, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d147, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21714 pattern childGuard
    simpa only [d147, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21716 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (18 : Int) + d5 pattern := by
  omega
theorem c21717 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (18 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21716 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21571 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21718 (pattern : Twelve) (guard : d1 pattern = 1) : d118 pattern ≤ (18 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21717 pattern childGuard
    simpa only [d118, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21582 pattern childGuard
    simpa only [d118, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21719 (pattern : Twelve) (guard : d1 pattern = 1) : d124 pattern ≤ (18 : Int) + d127 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d124, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21580 pattern childGuard
    simpa only [d124, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d124, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21718 pattern childGuard
    simpa only [d124, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21720 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (18 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21709 pattern childGuard
    simpa only [d117, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21617 pattern childGuard
    simpa only [d117, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21721 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (18 : Int) + d873 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21710 pattern childGuard
    simpa only [d119, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21720 pattern childGuard
    simpa only [d119, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21722 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (18 : Int) + d880 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21721 pattern childGuard
    simpa only [d125, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d125, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21723 (pattern : Twelve) (guard : d1 pattern = 1) : d133 pattern ≤ (18 : Int) + d887 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d133, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21719 pattern childGuard
    simpa only [d133, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d133, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21722 pattern childGuard
    simpa only [d133, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21724 (pattern : Twelve) (guard : d1 pattern = 1) : d142 pattern ≤ (18 : Int) + d896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d142, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21615 pattern childGuard
    simpa only [d142, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d142, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21723 pattern childGuard
    simpa only [d142, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21725 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (18 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21716 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21717 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21726 (pattern : Twelve) (guard : d1 pattern = 1) : d126 pattern ≤ (18 : Int) + d881 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d126, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21580 pattern childGuard
    simpa only [d126, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d126, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21725 pattern childGuard
    simpa only [d126, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21727 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (18 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21711 pattern childGuard
    simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21728 (pattern : Twelve) (guard : d1 pattern = 1) : d134 pattern ≤ (18 : Int) + d888 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d134, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21726 pattern childGuard
    simpa only [d134, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d134, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21727 pattern childGuard
    simpa only [d134, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21729 (pattern : Twelve) (guard : d1 pattern = 1) : d127 pattern ≤ (18 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21591 pattern childGuard
    simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21587 pattern childGuard
    simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21730 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21575 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21731 (pattern : Twelve) (guard : d1 pattern = 1) : d135 pattern ≤ (18 : Int) + d889 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21729 pattern childGuard
    simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21730 pattern childGuard
    simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21732 (pattern : Twelve) (guard : d1 pattern = 1) : d143 pattern ≤ (18 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21728 pattern childGuard
    simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21731 pattern childGuard
    simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21733 (pattern : Twelve) (guard : d1 pattern = 1) : d148 pattern ≤ (18 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21724 pattern childGuard
    simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21732 pattern childGuard
    simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21734 (pattern : Twelve) (guard : d1 pattern = 1) : d151 pattern ≤ (18 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21715 pattern childGuard
    simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21733 pattern childGuard
    simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21735 (pattern : Twelve) (guard : d1 pattern = 1) : d152 pattern ≤ (18 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21703 pattern childGuard
    simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21736 (pattern : Twelve) (guard : d1 pattern = 1) : d154 pattern ≤ (18 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21734 pattern childGuard
    simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21735 pattern childGuard
    simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21737 (pattern : Twelve) (guard : d1 pattern = 1) : d155 pattern ≤ (18 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21705 pattern childGuard
    simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21736 pattern childGuard
    simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21738 (pattern : Twelve) (guard : d1 pattern = 1) : d778 pattern ≤ (18 : Int) + d779 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d778, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21580 pattern childGuard
    simpa only [d778, d779, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d778, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21609 pattern childGuard
    simpa only [d778, d779, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21739 (pattern : Twelve) (guard : d1 pattern = 1) : d779 pattern ≤ (18 : Int) + d1247 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21622 pattern childGuard
    simpa only [d779, d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21609 pattern childGuard
    simpa only [d779, d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21740 (pattern : Twelve) (guard : d1 pattern = 1) : d782 pattern ≤ (18 : Int) + d1249 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d782, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21738 pattern childGuard
    simpa only [d782, d1249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d782, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21739 pattern childGuard
    simpa only [d782, d1249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21741 (pattern : Twelve) (guard : d1 pattern = 1) : d788 pattern ≤ (18 : Int) + d1253 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d788, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21578 pattern childGuard
    simpa only [d788, d1253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d788, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21740 pattern childGuard
    simpa only [d788, d1253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21742 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (18 : Int) + d1248 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21580 pattern childGuard
    simpa only [d38, d1248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21616 pattern childGuard
    simpa only [d38, d1248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21743 (pattern : Twelve) (guard : d1 pattern = 1) : d789 pattern ≤ (18 : Int) + d1254 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d789, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21742 pattern childGuard
    simpa only [d789, d1254, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d789, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21636 pattern childGuard
    simpa only [d789, d1254, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21744 (pattern : Twelve) (guard : d1 pattern = 1) : d794 pattern ≤ (18 : Int) + d1258 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d794, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21741 pattern childGuard
    simpa only [d794, d1258, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d794, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21743 pattern childGuard
    simpa only [d794, d1258, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21745 (pattern : Twelve) (guard : d1 pattern = 1) : d783 pattern ≤ (18 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d783, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21668 pattern childGuard
    simpa only [d783, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d783, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21649 pattern childGuard
    simpa only [d783, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21746 (pattern : Twelve) (guard : d1 pattern = 1) : d790 pattern ≤ (18 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d790, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21745 pattern childGuard
    simpa only [d790, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d790, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21673 pattern childGuard
    simpa only [d790, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21747 (pattern : Twelve) (guard : d1 pattern = 1) : d795 pattern ≤ (18 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d795, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21746 pattern childGuard
    simpa only [d795, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d795, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21679 pattern childGuard
    simpa only [d795, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21748 (pattern : Twelve) (guard : d1 pattern = 1) : d798 pattern ≤ (18 : Int) + d1261 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d798, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21744 pattern childGuard
    simpa only [d798, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d798, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21747 pattern childGuard
    simpa only [d798, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21749 (pattern : Twelve) (guard : d1 pattern = 1) : d799 pattern ≤ (18 : Int) + d1261 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d799, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21744 pattern childGuard
    simpa only [d799, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d799, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21680 pattern childGuard
    simpa only [d799, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21750 (pattern : Twelve) (guard : d1 pattern = 1) : d802 pattern ≤ (18 : Int) + d1261 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21748 pattern childGuard
    simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21749 pattern childGuard
    simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21751 (pattern : Twelve) (guard : d1 pattern = 1) : d780 pattern ≤ (18 : Int) + d780 pattern := by
  omega
theorem c21752 (pattern : Twelve) (guard : d1 pattern = 1) : d784 pattern ≤ (18 : Int) + d1250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d784, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21620 pattern childGuard
    simpa only [d784, d1250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d784, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21751 pattern childGuard
    simpa only [d784, d1250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21753 (pattern : Twelve) (guard : d1 pattern = 1) : d791 pattern ≤ (18 : Int) + d1255 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d791, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21668 pattern childGuard
    simpa only [d791, d1255, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d791, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21752 pattern childGuard
    simpa only [d791, d1255, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21754 (pattern : Twelve) (guard : d1 pattern = 1) : d796 pattern ≤ (18 : Int) + d1259 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d796, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21753 pattern childGuard
    simpa only [d796, d1259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d796, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21679 pattern childGuard
    simpa only [d796, d1259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21755 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (18 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21619 pattern childGuard
    simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21756 (pattern : Twelve) (guard : d1 pattern = 1) : d781 pattern ≤ (18 : Int) + d781 pattern := by
  omega
theorem c21757 (pattern : Twelve) (guard : d1 pattern = 1) : d785 pattern ≤ (18 : Int) + d1251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d785, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21755 pattern childGuard
    simpa only [d785, d1251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d785, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21756 pattern childGuard
    simpa only [d785, d1251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21758 (pattern : Twelve) (guard : d1 pattern = 1) : d792 pattern ≤ (18 : Int) + d1256 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d792, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21675 pattern childGuard
    simpa only [d792, d1256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d792, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21757 pattern childGuard
    simpa only [d792, d1256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21759 (pattern : Twelve) (guard : d1 pattern = 1) : d786 pattern ≤ (18 : Int) + d787 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d786, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21755 pattern childGuard
    simpa only [d786, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d786, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d786, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21760 (pattern : Twelve) (guard : d1 pattern = 1) : d787 pattern ≤ (18 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d787, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21677 pattern childGuard
    simpa only [d787, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d787, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d787, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21761 (pattern : Twelve) (guard : d1 pattern = 1) : d793 pattern ≤ (18 : Int) + d1257 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d793, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21759 pattern childGuard
    simpa only [d793, d1257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d793, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21760 pattern childGuard
    simpa only [d793, d1257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21762 (pattern : Twelve) (guard : d1 pattern = 1) : d797 pattern ≤ (18 : Int) + d1260 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d797, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21758 pattern childGuard
    simpa only [d797, d1260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d797, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21761 pattern childGuard
    simpa only [d797, d1260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21763 (pattern : Twelve) (guard : d1 pattern = 1) : d800 pattern ≤ (18 : Int) + d1262 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d800, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21754 pattern childGuard
    simpa only [d800, d1262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d800, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21762 pattern childGuard
    simpa only [d800, d1262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21764 (pattern : Twelve) (guard : d1 pattern = 1) : d801 pattern ≤ (18 : Int) + d1263 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d801, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21680 pattern childGuard
    simpa only [d801, d1263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d801, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d801, d1263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21765 (pattern : Twelve) (guard : d1 pattern = 1) : d803 pattern ≤ (18 : Int) + d1264 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d803, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21763 pattern childGuard
    simpa only [d803, d1264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d803, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21764 pattern childGuard
    simpa only [d803, d1264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21766 (pattern : Twelve) (guard : d1 pattern = 1) : d804 pattern ≤ (18 : Int) + d1265 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d804, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21750 pattern childGuard
    simpa only [d804, d1265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d804, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21765 pattern childGuard
    simpa only [d804, d1265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21767 (pattern : Twelve) (guard : d1 pattern = 1) : d805 pattern ≤ (18 : Int) + d1266 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d805, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21737 pattern childGuard
    simpa only [d805, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d805, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21766 pattern childGuard
    simpa only [d805, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21768 (pattern : Twelve) (guard : d1 pattern = 1) : d806 pattern ≤ (18 : Int) + d1267 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d806, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21685 pattern childGuard
    simpa only [d806, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d806, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21767 pattern childGuard
    simpa only [d806, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21769 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (18 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21538 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21553 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21770 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (18 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21539 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21769 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21771 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (18 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21770 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21687 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21772 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (18 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21543 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21686 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21773 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (18 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21772 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21687 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21774 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (18 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21771 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21773 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21775 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (18 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21540 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21774 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21776 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (18 : Int) + d6 pattern := by
  change (0 : Int) ≤ (18 : Int) + 6
  decide
theorem c21777 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (18 : Int) + d6 pattern := by
  change (2 : Int) ≤ (18 : Int) + 6
  decide
theorem c21778 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21776 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21777 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21779 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (18 : Int) + d6 pattern := by
  change (1 : Int) ≤ (18 : Int) + 6
  decide
theorem c21780 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21779 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21570 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21781 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21778 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21780 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21782 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21777 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21573 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21783 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21782 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21572 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21784 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21781 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21783 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21785 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21783 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21786 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21784 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21785 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21787 (pattern : Twelve) (guard : d1 pattern = 1) : d839 pattern ≤ (18 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21552 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21786 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21788 (pattern : Twelve) (guard : d1 pattern = 1) : d853 pattern ≤ (18 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21775 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21787 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21789 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (18 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21556 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21709 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21790 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (18 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21579 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21789 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21791 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (18 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21770 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21790 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21792 (pattern : Twelve) (guard : d1 pattern = 1) : d818 pattern ≤ (18 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21772 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21793 (pattern : Twelve) (guard : d1 pattern = 1) : d826 pattern ≤ (18 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21791 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21792 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21794 (pattern : Twelve) (guard : d1 pattern = 1) : d840 pattern ≤ (18 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21604 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21793 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21795 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (18 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21552 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21796 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (18 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21592 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21795 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21797 (pattern : Twelve) (guard : d1 pattern = 1) : d841 pattern ≤ (18 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21796 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21786 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21798 (pattern : Twelve) (guard : d1 pattern = 1) : d854 pattern ≤ (18 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21794 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21797 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21799 (pattern : Twelve) (guard : d1 pattern = 1) : d861 pattern ≤ (18 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21788 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21798 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21800 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (18 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21772 pattern childGuard
    simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21711 pattern childGuard
    simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21801 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (18 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21791 pattern childGuard
    simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21800 pattern childGuard
    simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21802 (pattern : Twelve) (guard : d1 pattern = 1) : d842 pattern ≤ (18 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21581 pattern childGuard
    simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21801 pattern childGuard
    simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21803 (pattern : Twelve) (guard : d1 pattern = 1) : d843 pattern ≤ (18 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21592 pattern childGuard
    simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21786 pattern childGuard
    simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21804 (pattern : Twelve) (guard : d1 pattern = 1) : d855 pattern ≤ (18 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21802 pattern childGuard
    simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21803 pattern childGuard
    simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21805 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (18 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21618 pattern childGuard
    simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21629 pattern childGuard
    simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21806 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (18 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21790 pattern childGuard
    simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21805 pattern childGuard
    simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21807 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (18 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21621 pattern childGuard
    simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21710 pattern childGuard
    simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21808 (pattern : Twelve) (guard : d1 pattern = 1) : d820 pattern ≤ (18 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21807 pattern childGuard
    simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21809 (pattern : Twelve) (guard : d1 pattern = 1) : d829 pattern ≤ (18 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21806 pattern childGuard
    simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21808 pattern childGuard
    simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21810 (pattern : Twelve) (guard : d1 pattern = 1) : d844 pattern ≤ (18 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21627 pattern childGuard
    simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21809 pattern childGuard
    simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21811 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (18 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21631 pattern childGuard
    simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21651 pattern childGuard
    simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21812 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21783 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21583 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21813 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21583 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21814 (pattern : Twelve) (guard : d1 pattern = 1) : d831 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21812 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21813 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21815 (pattern : Twelve) (guard : d1 pattern = 1) : d845 pattern ≤ (18 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21811 pattern childGuard
    simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21814 pattern childGuard
    simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21816 (pattern : Twelve) (guard : d1 pattern = 1) : d856 pattern ≤ (18 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21810 pattern childGuard
    simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21815 pattern childGuard
    simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21817 (pattern : Twelve) (guard : d1 pattern = 1) : d862 pattern ≤ (18 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21804 pattern childGuard
    simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21816 pattern childGuard
    simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21818 (pattern : Twelve) (guard : d1 pattern = 1) : d863 pattern ≤ (18 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21798 pattern childGuard
    simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21819 (pattern : Twelve) (guard : d1 pattern = 1) : d867 pattern ≤ (18 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21817 pattern childGuard
    simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21818 pattern childGuard
    simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21820 (pattern : Twelve) (guard : d1 pattern = 1) : d869 pattern ≤ (18 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21799 pattern childGuard
    simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21819 pattern childGuard
    simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21821 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (18 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21552 pattern childGuard
    simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21580 pattern childGuard
    simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21822 (pattern : Twelve) (guard : d1 pattern = 1) : d846 pattern ≤ (18 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21821 pattern childGuard
    simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21786 pattern childGuard
    simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21823 (pattern : Twelve) (guard : d1 pattern = 1) : d857 pattern ≤ (18 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21775 pattern childGuard
    simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21822 pattern childGuard
    simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21824 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (18 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21687 pattern childGuard
    simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21825 (pattern : Twelve) (guard : d1 pattern = 1) : d832 pattern ≤ (18 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21791 pattern childGuard
    simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21824 pattern childGuard
    simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21826 (pattern : Twelve) (guard : d1 pattern = 1) : d847 pattern ≤ (18 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21604 pattern childGuard
    simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21825 pattern childGuard
    simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21827 (pattern : Twelve) (guard : d1 pattern = 1) : d833 pattern ≤ (18 : Int) + d1290 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21592 pattern childGuard
    simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21626 pattern childGuard
    simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21828 (pattern : Twelve) (guard : d1 pattern = 1) : d848 pattern ≤ (18 : Int) + d1302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21827 pattern childGuard
    simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21786 pattern childGuard
    simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21829 (pattern : Twelve) (guard : d1 pattern = 1) : d858 pattern ≤ (18 : Int) + d1310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21826 pattern childGuard
    simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21828 pattern childGuard
    simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21830 (pattern : Twelve) (guard : d1 pattern = 1) : d864 pattern ≤ (18 : Int) + d1316 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21823 pattern childGuard
    simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21829 pattern childGuard
    simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21831 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (18 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21687 pattern childGuard
    simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21711 pattern childGuard
    simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21832 (pattern : Twelve) (guard : d1 pattern = 1) : d834 pattern ≤ (18 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21791 pattern childGuard
    simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21831 pattern childGuard
    simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21833 (pattern : Twelve) (guard : d1 pattern = 1) : d849 pattern ≤ (18 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21581 pattern childGuard
    simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21832 pattern childGuard
    simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21834 (pattern : Twelve) (guard : d1 pattern = 1) : d835 pattern ≤ (18 : Int) + d1291 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21592 pattern childGuard
    simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21620 pattern childGuard
    simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21835 (pattern : Twelve) (guard : d1 pattern = 1) : d850 pattern ≤ (18 : Int) + d1303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21834 pattern childGuard
    simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21786 pattern childGuard
    simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21836 (pattern : Twelve) (guard : d1 pattern = 1) : d859 pattern ≤ (18 : Int) + d1311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21833 pattern childGuard
    simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21835 pattern childGuard
    simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21837 (pattern : Twelve) (guard : d1 pattern = 1) : d836 pattern ≤ (18 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21806 pattern childGuard
    simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21727 pattern childGuard
    simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21838 (pattern : Twelve) (guard : d1 pattern = 1) : d851 pattern ≤ (18 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21627 pattern childGuard
    simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21837 pattern childGuard
    simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21839 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (18 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21631 pattern childGuard
    simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21755 pattern childGuard
    simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
