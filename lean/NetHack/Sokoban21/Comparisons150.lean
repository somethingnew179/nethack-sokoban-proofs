/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons149
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c21000 (pattern : Twelve) (guard : d1 pattern = 1) : d136 pattern ≤ (2 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d136, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d136, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d136, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20996 pattern childGuard
    simpa only [d136, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21001 (pattern : Twelve) (guard : d1 pattern = 1) : d144 pattern ≤ (2 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d144, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20285 pattern childGuard
    simpa only [d144, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d144, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21000 pattern childGuard
    simpa only [d144, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21002 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (2 : Int) + d36 pattern := by
  omega
theorem c21003 (pattern : Twelve) (guard : d1 pattern = 1) : d130 pattern ≤ (2 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d130, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20989 pattern childGuard
    simpa only [d130, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d130, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21002 pattern childGuard
    simpa only [d130, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21004 (pattern : Twelve) (guard : d1 pattern = 1) : d139 pattern ≤ (2 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d139, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20309 pattern childGuard
    simpa only [d139, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d139, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21003 pattern childGuard
    simpa only [d139, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21005 (pattern : Twelve) (guard : d1 pattern = 1) : d138 pattern ≤ (2 : Int) + d78 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d138, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20309 pattern childGuard
    simpa only [d138, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d138, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20996 pattern childGuard
    simpa only [d138, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21006 (pattern : Twelve) (guard : d1 pattern = 1) : d146 pattern ≤ (2 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d146, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21004 pattern childGuard
    simpa only [d146, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d146, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21005 pattern childGuard
    simpa only [d146, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21007 (pattern : Twelve) (guard : d1 pattern = 1) : d150 pattern ≤ (2 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d150, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21001 pattern childGuard
    simpa only [d150, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d150, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21006 pattern childGuard
    simpa only [d150, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21008 (pattern : Twelve) (guard : d1 pattern = 1) : d153 pattern ≤ (2 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d153, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20999 pattern childGuard
    simpa only [d153, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d153, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21007 pattern childGuard
    simpa only [d153, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21009 (pattern : Twelve) (guard : d1 pattern = 1) : d122 pattern ≤ (2 : Int) + d37 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d122, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d122, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d122, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14219 pattern childGuard
    simpa only [d122, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21010 (pattern : Twelve) (guard : d1 pattern = 1) : d131 pattern ≤ (2 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d131, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20989 pattern childGuard
    simpa only [d131, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d131, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21009 pattern childGuard
    simpa only [d131, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21011 (pattern : Twelve) (guard : d1 pattern = 1) : d140 pattern ≤ (2 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d140, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d140, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d140, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21010 pattern childGuard
    simpa only [d140, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21012 (pattern : Twelve) (guard : d1 pattern = 1) : d123 pattern ≤ (2 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d123, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d123, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d123, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13388 pattern childGuard
    simpa only [d123, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21013 (pattern : Twelve) (guard : d1 pattern = 1) : d132 pattern ≤ (2 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21012 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21014 (pattern : Twelve) (guard : d1 pattern = 1) : d141 pattern ≤ (2 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d141, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21013 pattern childGuard
    simpa only [d141, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d141, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20996 pattern childGuard
    simpa only [d141, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21015 (pattern : Twelve) (guard : d1 pattern = 1) : d147 pattern ≤ (2 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d147, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21011 pattern childGuard
    simpa only [d147, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d147, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21014 pattern childGuard
    simpa only [d147, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21016 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (2 : Int) + d4 pattern := by
  change (5 : Int) ≤ (2 : Int) + 4
  decide
theorem c21017 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (2 : Int) + d4 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21016 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13369 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21018 (pattern : Twelve) (guard : d1 pattern = 1) : d118 pattern ≤ (2 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21016 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21017 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21019 (pattern : Twelve) (guard : d1 pattern = 1) : d124 pattern ≤ (2 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d124, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d124, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d124, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21018 pattern childGuard
    simpa only [d124, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21020 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (2 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13388 pattern childGuard
    simpa only [d117, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14219 pattern childGuard
    simpa only [d117, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21021 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13388 pattern childGuard
    simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21020 pattern childGuard
    simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21022 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (2 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21021 pattern childGuard
    simpa only [d125, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d125, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21023 (pattern : Twelve) (guard : d1 pattern = 1) : d133 pattern ≤ (2 : Int) + d60 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d133, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21019 pattern childGuard
    simpa only [d133, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d133, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21022 pattern childGuard
    simpa only [d133, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21024 (pattern : Twelve) (guard : d1 pattern = 1) : d142 pattern ≤ (2 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d142, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20326 pattern childGuard
    simpa only [d142, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d142, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21023 pattern childGuard
    simpa only [d142, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21025 (pattern : Twelve) (guard : d1 pattern = 1) : d126 pattern ≤ (2 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d126, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d126, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d126, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21016 pattern childGuard
    simpa only [d126, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21026 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (2 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13388 pattern childGuard
    simpa only [d47, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d47, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21027 (pattern : Twelve) (guard : d1 pattern = 1) : d134 pattern ≤ (2 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d134, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21025 pattern childGuard
    simpa only [d134, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d134, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21026 pattern childGuard
    simpa only [d134, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21028 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (2 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21017 pattern childGuard
    simpa only [d22, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14357 pattern childGuard
    simpa only [d22, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21029 (pattern : Twelve) (guard : d1 pattern = 1) : d127 pattern ≤ (2 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13590 pattern childGuard
    simpa only [d127, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21028 pattern childGuard
    simpa only [d127, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21030 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (2 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13388 pattern childGuard
    simpa only [d12, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21016 pattern childGuard
    simpa only [d12, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21031 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (2 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14219 pattern childGuard
    simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13371 pattern childGuard
    simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21032 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21030 pattern childGuard
    simpa only [d20, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21031 pattern childGuard
    simpa only [d20, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21033 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (2 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21032 pattern childGuard
    simpa only [d128, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d128, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21034 (pattern : Twelve) (guard : d1 pattern = 1) : d135 pattern ≤ (2 : Int) + d61 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d135, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21029 pattern childGuard
    simpa only [d135, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d135, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21033 pattern childGuard
    simpa only [d135, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21035 (pattern : Twelve) (guard : d1 pattern = 1) : d143 pattern ≤ (2 : Int) + d82 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d143, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21027 pattern childGuard
    simpa only [d143, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d143, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21034 pattern childGuard
    simpa only [d143, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21036 (pattern : Twelve) (guard : d1 pattern = 1) : d148 pattern ≤ (2 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d148, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21024 pattern childGuard
    simpa only [d148, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d148, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21035 pattern childGuard
    simpa only [d148, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21037 (pattern : Twelve) (guard : d1 pattern = 1) : d151 pattern ≤ (2 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d151, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21015 pattern childGuard
    simpa only [d151, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d151, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21036 pattern childGuard
    simpa only [d151, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21038 (pattern : Twelve) (guard : d1 pattern = 1) : d152 pattern ≤ (2 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d152, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21006 pattern childGuard
    simpa only [d152, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d152, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d152, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21039 (pattern : Twelve) (guard : d1 pattern = 1) : d154 pattern ≤ (2 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d154, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21037 pattern childGuard
    simpa only [d154, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d154, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21038 pattern childGuard
    simpa only [d154, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21040 (pattern : Twelve) (guard : d1 pattern = 1) : d155 pattern ≤ (2 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d155, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21008 pattern childGuard
    simpa only [d155, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d155, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21039 pattern childGuard
    simpa only [d155, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21041 (pattern : Twelve) (guard : d1 pattern = 1) : d778 pattern ≤ (2 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d778, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13281 pattern childGuard
    simpa only [d778, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d778, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d778, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21042 (pattern : Twelve) (guard : d1 pattern = 1) : d779 pattern ≤ (2 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13299 pattern childGuard
    simpa only [d779, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d779, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21043 (pattern : Twelve) (guard : d1 pattern = 1) : d782 pattern ≤ (2 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d782, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21041 pattern childGuard
    simpa only [d782, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d782, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21042 pattern childGuard
    simpa only [d782, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21044 (pattern : Twelve) (guard : d1 pattern = 1) : d788 pattern ≤ (2 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d788, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13281 pattern childGuard
    simpa only [d788, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d788, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21043 pattern childGuard
    simpa only [d788, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21045 (pattern : Twelve) (guard : d1 pattern = 1) : d789 pattern ≤ (2 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d789, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13294 pattern childGuard
    simpa only [d789, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d789, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13311 pattern childGuard
    simpa only [d789, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21046 (pattern : Twelve) (guard : d1 pattern = 1) : d794 pattern ≤ (2 : Int) + d97 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d794, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21044 pattern childGuard
    simpa only [d794, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d794, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21045 pattern childGuard
    simpa only [d794, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21047 (pattern : Twelve) (guard : d1 pattern = 1) : d44 pattern ≤ (2 : Int) + d31 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13281 pattern childGuard
    simpa only [d44, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13463 pattern childGuard
    simpa only [d44, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21048 (pattern : Twelve) (guard : d1 pattern = 1) : d783 pattern ≤ (2 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d783, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13294 pattern childGuard
    simpa only [d783, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d783, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21047 pattern childGuard
    simpa only [d783, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21049 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (2 : Int) + d43 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d47, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13469 pattern childGuard
    simpa only [d47, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21050 (pattern : Twelve) (guard : d1 pattern = 1) : d69 pattern ≤ (2 : Int) + d62 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13294 pattern childGuard
    simpa only [d69, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21049 pattern childGuard
    simpa only [d69, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21051 (pattern : Twelve) (guard : d1 pattern = 1) : d790 pattern ≤ (2 : Int) + d83 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d790, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21048 pattern childGuard
    simpa only [d790, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d790, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21050 pattern childGuard
    simpa only [d790, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21052 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (2 : Int) + d44 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d48, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14487 pattern childGuard
    simpa only [d48, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21053 (pattern : Twelve) (guard : d1 pattern = 1) : d70 pattern ≤ (2 : Int) + d63 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13294 pattern childGuard
    simpa only [d70, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21052 pattern childGuard
    simpa only [d70, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21054 (pattern : Twelve) (guard : d1 pattern = 1) : d90 pattern ≤ (2 : Int) + d84 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21053 pattern childGuard
    simpa only [d90, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13344 pattern childGuard
    simpa only [d90, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21055 (pattern : Twelve) (guard : d1 pattern = 1) : d795 pattern ≤ (2 : Int) + d98 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d795, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21051 pattern childGuard
    simpa only [d795, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d795, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21054 pattern childGuard
    simpa only [d795, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21056 (pattern : Twelve) (guard : d1 pattern = 1) : d798 pattern ≤ (2 : Int) + d106 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d798, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21046 pattern childGuard
    simpa only [d798, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d798, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21055 pattern childGuard
    simpa only [d798, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21057 (pattern : Twelve) (guard : d1 pattern = 1) : d799 pattern ≤ (2 : Int) + d107 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d799, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21046 pattern childGuard
    simpa only [d799, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d799, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13346 pattern childGuard
    simpa only [d799, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21058 (pattern : Twelve) (guard : d1 pattern = 1) : d802 pattern ≤ (2 : Int) + d112 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d802, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21056 pattern childGuard
    simpa only [d802, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d802, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21057 pattern childGuard
    simpa only [d802, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21059 (pattern : Twelve) (guard : d1 pattern = 1) : d780 pattern ≤ (2 : Int) + d46 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d780, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d780, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d780, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13303 pattern childGuard
    simpa only [d780, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21060 (pattern : Twelve) (guard : d1 pattern = 1) : d784 pattern ≤ (2 : Int) + d67 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d784, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13294 pattern childGuard
    simpa only [d784, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d784, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21059 pattern childGuard
    simpa only [d784, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21061 (pattern : Twelve) (guard : d1 pattern = 1) : d791 pattern ≤ (2 : Int) + d87 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d791, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13294 pattern childGuard
    simpa only [d791, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d791, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21060 pattern childGuard
    simpa only [d791, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21062 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (2 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d48, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13369 pattern childGuard
    simpa only [d48, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21063 (pattern : Twelve) (guard : d1 pattern = 1) : d70 pattern ≤ (2 : Int) + d68 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13294 pattern childGuard
    simpa only [d70, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21062 pattern childGuard
    simpa only [d70, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21064 (pattern : Twelve) (guard : d1 pattern = 1) : d90 pattern ≤ (2 : Int) + d88 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21063 pattern childGuard
    simpa only [d90, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13344 pattern childGuard
    simpa only [d90, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21065 (pattern : Twelve) (guard : d1 pattern = 1) : d796 pattern ≤ (2 : Int) + d100 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d796, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21061 pattern childGuard
    simpa only [d796, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d796, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21064 pattern childGuard
    simpa only [d796, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21066 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (2 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21062 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13341 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21067 (pattern : Twelve) (guard : d1 pattern = 1) : d781 pattern ≤ (2 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d781, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13303 pattern childGuard
    simpa only [d781, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d781, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d781, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21068 (pattern : Twelve) (guard : d1 pattern = 1) : d785 pattern ≤ (2 : Int) + d69 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d785, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21062 pattern childGuard
    simpa only [d785, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d785, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21067 pattern childGuard
    simpa only [d785, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21069 (pattern : Twelve) (guard : d1 pattern = 1) : d792 pattern ≤ (2 : Int) + d89 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d792, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21066 pattern childGuard
    simpa only [d792, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d792, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21068 pattern childGuard
    simpa only [d792, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21070 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13369 pattern childGuard
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21071 (pattern : Twelve) (guard : d1 pattern = 1) : d786 pattern ≤ (2 : Int) + d70 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d786, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21062 pattern childGuard
    simpa only [d786, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d786, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21070 pattern childGuard
    simpa only [d786, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21072 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13369 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14357 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21073 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (2 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13305 pattern childGuard
    simpa only [d49, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21072 pattern childGuard
    simpa only [d49, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21074 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21072 pattern childGuard
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21075 (pattern : Twelve) (guard : d1 pattern = 1) : d787 pattern ≤ (2 : Int) + d71 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d787, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21073 pattern childGuard
    simpa only [d787, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d787, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21074 pattern childGuard
    simpa only [d787, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21076 (pattern : Twelve) (guard : d1 pattern = 1) : d793 pattern ≤ (2 : Int) + d90 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d793, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21071 pattern childGuard
    simpa only [d793, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d793, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21075 pattern childGuard
    simpa only [d793, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21077 (pattern : Twelve) (guard : d1 pattern = 1) : d797 pattern ≤ (2 : Int) + d101 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d797, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21069 pattern childGuard
    simpa only [d797, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d797, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21076 pattern childGuard
    simpa only [d797, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21078 (pattern : Twelve) (guard : d1 pattern = 1) : d800 pattern ≤ (2 : Int) + d108 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d800, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21065 pattern childGuard
    simpa only [d800, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d800, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21077 pattern childGuard
    simpa only [d800, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21079 (pattern : Twelve) (guard : d1 pattern = 1) : d801 pattern ≤ (2 : Int) + d109 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d801, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13346 pattern childGuard
    simpa only [d801, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d801, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d801, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21080 (pattern : Twelve) (guard : d1 pattern = 1) : d803 pattern ≤ (2 : Int) + d113 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d803, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21078 pattern childGuard
    simpa only [d803, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d803, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21079 pattern childGuard
    simpa only [d803, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21081 (pattern : Twelve) (guard : d1 pattern = 1) : d804 pattern ≤ (2 : Int) + d115 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d804, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21058 pattern childGuard
    simpa only [d804, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d804, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21080 pattern childGuard
    simpa only [d804, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21082 (pattern : Twelve) (guard : d1 pattern = 1) : d805 pattern ≤ (2 : Int) + d116 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d805, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21040 pattern childGuard
    simpa only [d805, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d805, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21081 pattern childGuard
    simpa only [d805, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21083 (pattern : Twelve) (guard : d1879 pattern = 1) : d806 pattern ≤ (2 : Int) + d116 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1879, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20983 pattern childGuard
    simpa only [d1879, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1879, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21082 pattern childGuard
    simpa only [d1879, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21084 (pattern : Twelve) (guard : d0 pattern = 1) : d871 pattern ≤ (2 : Int) + d871 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c21085 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13320 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14333 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21086 (pattern : Twelve) (guard : d1 pattern = 1) : d874 pattern ≤ (2 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d874, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21085 pattern childGuard
    simpa only [d874, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21087 (pattern : Twelve) (guard : d1 pattern = 1) : d875 pattern ≤ (2 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13356 pattern childGuard
    simpa only [d875, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21085 pattern childGuard
    simpa only [d875, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21088 (pattern : Twelve) (guard : d1 pattern = 1) : d882 pattern ≤ (2 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21086 pattern childGuard
    simpa only [d882, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21087 pattern childGuard
    simpa only [d882, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21089 (pattern : Twelve) (guard : d1 pattern = 1) : d890 pattern ≤ (2 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d890, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d890, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d890, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21088 pattern childGuard
    simpa only [d890, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21090 (pattern : Twelve) (guard : d1 pattern = 1) : d876 pattern ≤ (2 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d876, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13418 pattern childGuard
    simpa only [d876, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d876, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13373 pattern childGuard
    simpa only [d876, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21091 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (2 : Int) + d42 pattern := by
  omega
theorem c21092 (pattern : Twelve) (guard : d1 pattern = 1) : d883 pattern ≤ (2 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d883, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21090 pattern childGuard
    simpa only [d883, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d883, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21091 pattern childGuard
    simpa only [d883, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21093 (pattern : Twelve) (guard : d1 pattern = 1) : d891 pattern ≤ (2 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d891, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d891, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d891, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21092 pattern childGuard
    simpa only [d891, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21094 (pattern : Twelve) (guard : d1 pattern = 1) : d898 pattern ≤ (2 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d898, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21089 pattern childGuard
    simpa only [d898, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d898, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21093 pattern childGuard
    simpa only [d898, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21095 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13388 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13331 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21096 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13389 pattern childGuard
    simpa only [d815, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21095 pattern childGuard
    simpa only [d815, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21097 (pattern : Twelve) (guard : d1 pattern = 1) : d877 pattern ≤ (2 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d877, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d877, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d877, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21096 pattern childGuard
    simpa only [d877, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21098 (pattern : Twelve) (guard : d1 pattern = 1) : d818 pattern ≤ (2 : Int) + d818 pattern := by
  omega
theorem c21099 (pattern : Twelve) (guard : d1 pattern = 1) : d884 pattern ≤ (2 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d884, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21097 pattern childGuard
    simpa only [d884, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d884, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21098 pattern childGuard
    simpa only [d884, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21100 (pattern : Twelve) (guard : d1 pattern = 1) : d892 pattern ≤ (2 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d892, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20309 pattern childGuard
    simpa only [d892, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d892, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21099 pattern childGuard
    simpa only [d892, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21101 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (2 : Int) + d827 pattern := by
  omega
theorem c21102 (pattern : Twelve) (guard : d1 pattern = 1) : d893 pattern ≤ (2 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d893, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21101 pattern childGuard
    simpa only [d893, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d893, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21092 pattern childGuard
    simpa only [d893, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21103 (pattern : Twelve) (guard : d1 pattern = 1) : d899 pattern ≤ (2 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d899, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21100 pattern childGuard
    simpa only [d899, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d899, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21102 pattern childGuard
    simpa only [d899, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21104 (pattern : Twelve) (guard : d1 pattern = 1) : d902 pattern ≤ (2 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d902, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21094 pattern childGuard
    simpa only [d902, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d902, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21103 pattern childGuard
    simpa only [d902, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21105 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (2 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14219 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14314 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21106 (pattern : Twelve) (guard : d1 pattern = 1) : d878 pattern ≤ (2 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d878, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13356 pattern childGuard
    simpa only [d878, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d878, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21105 pattern childGuard
    simpa only [d878, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21107 (pattern : Twelve) (guard : d1 pattern = 1) : d885 pattern ≤ (2 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21097 pattern childGuard
    simpa only [d885, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21106 pattern childGuard
    simpa only [d885, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21108 (pattern : Twelve) (guard : d1 pattern = 1) : d894 pattern ≤ (2 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d894, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d894, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d894, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21107 pattern childGuard
    simpa only [d894, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21109 (pattern : Twelve) (guard : d1 pattern = 1) : d879 pattern ≤ (2 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d879, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21021 pattern childGuard
    simpa only [d879, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21110 (pattern : Twelve) (guard : d1 pattern = 1) : d886 pattern ≤ (2 : Int) + d34 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13328 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21109 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21111 (pattern : Twelve) (guard : d1 pattern = 1) : d895 pattern ≤ (2 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d895, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21110 pattern childGuard
    simpa only [d895, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d895, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21092 pattern childGuard
    simpa only [d895, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21112 (pattern : Twelve) (guard : d1 pattern = 1) : d900 pattern ≤ (2 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d900, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21108 pattern childGuard
    simpa only [d900, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d900, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21111 pattern childGuard
    simpa only [d900, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21113 (pattern : Twelve) (guard : d1 pattern = 1) : d873 pattern ≤ (2 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21020 pattern childGuard
    simpa only [d873, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14314 pattern childGuard
    simpa only [d873, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21114 (pattern : Twelve) (guard : d1 pattern = 1) : d880 pattern ≤ (2 : Int) + d820 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d880, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21113 pattern childGuard
    simpa only [d880, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d880, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d880, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21115 (pattern : Twelve) (guard : d1 pattern = 1) : d887 pattern ≤ (2 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d887, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21029 pattern childGuard
    simpa only [d887, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d887, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21114 pattern childGuard
    simpa only [d887, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21116 (pattern : Twelve) (guard : d1 pattern = 1) : d896 pattern ≤ (2 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d896, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20326 pattern childGuard
    simpa only [d896, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d896, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21115 pattern childGuard
    simpa only [d896, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21117 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (2 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21016 pattern childGuard
    simpa only [d14, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13371 pattern childGuard
    simpa only [d14, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21118 (pattern : Twelve) (guard : d1 pattern = 1) : d118 pattern ≤ (2 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21016 pattern childGuard
    simpa only [d118, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21117 pattern childGuard
    simpa only [d118, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21119 (pattern : Twelve) (guard : d1 pattern = 1) : d881 pattern ≤ (2 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13590 pattern childGuard
    simpa only [d881, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21118 pattern childGuard
    simpa only [d881, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21120 (pattern : Twelve) (guard : d1 pattern = 1) : d888 pattern ≤ (2 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21119 pattern childGuard
    simpa only [d888, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21022 pattern childGuard
    simpa only [d888, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21121 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (2 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13458 pattern childGuard
    simpa only [d42, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13469 pattern childGuard
    simpa only [d42, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21122 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13469 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21123 (pattern : Twelve) (guard : d1 pattern = 1) : d889 pattern ≤ (2 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d889, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21121 pattern childGuard
    simpa only [d889, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d889, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21122 pattern childGuard
    simpa only [d889, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21124 (pattern : Twelve) (guard : d1 pattern = 1) : d897 pattern ≤ (2 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d897, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21120 pattern childGuard
    simpa only [d897, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d897, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21123 pattern childGuard
    simpa only [d897, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21125 (pattern : Twelve) (guard : d1 pattern = 1) : d901 pattern ≤ (2 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d901, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21116 pattern childGuard
    simpa only [d901, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d901, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21124 pattern childGuard
    simpa only [d901, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21126 (pattern : Twelve) (guard : d1 pattern = 1) : d903 pattern ≤ (2 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d903, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21112 pattern childGuard
    simpa only [d903, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d903, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21125 pattern childGuard
    simpa only [d903, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21127 (pattern : Twelve) (guard : d1 pattern = 1) : d904 pattern ≤ (2 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d904, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21103 pattern childGuard
    simpa only [d904, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d904, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d904, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21128 (pattern : Twelve) (guard : d1 pattern = 1) : d905 pattern ≤ (2 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d905, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21126 pattern childGuard
    simpa only [d905, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d905, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21127 pattern childGuard
    simpa only [d905, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21129 (pattern : Twelve) (guard : d1 pattern = 1) : d906 pattern ≤ (2 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d906, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21104 pattern childGuard
    simpa only [d906, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d906, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21128 pattern childGuard
    simpa only [d906, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21130 (pattern : Twelve) (guard : d1 pattern = 1) : d1247 pattern ≤ (2 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1247, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13364 pattern childGuard
    simpa only [d1247, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1247, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d1247, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21131 (pattern : Twelve) (guard : d1 pattern = 1) : d1249 pattern ≤ (2 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1249, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21042 pattern childGuard
    simpa only [d1249, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1249, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21130 pattern childGuard
    simpa only [d1249, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21132 (pattern : Twelve) (guard : d1 pattern = 1) : d1253 pattern ≤ (2 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1253, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13281 pattern childGuard
    simpa only [d1253, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1253, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21131 pattern childGuard
    simpa only [d1253, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21133 (pattern : Twelve) (guard : d1 pattern = 1) : d1248 pattern ≤ (2 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1248, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13299 pattern childGuard
    simpa only [d1248, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1248, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d1248, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21134 (pattern : Twelve) (guard : d1 pattern = 1) : d1254 pattern ≤ (2 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1254, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21133 pattern childGuard
    simpa only [d1254, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1254, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13376 pattern childGuard
    simpa only [d1254, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21135 (pattern : Twelve) (guard : d1 pattern = 1) : d1258 pattern ≤ (2 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1258, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21132 pattern childGuard
    simpa only [d1258, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1258, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21134 pattern childGuard
    simpa only [d1258, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21136 (pattern : Twelve) (guard : d1 pattern = 1) : d1261 pattern ≤ (2 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1261, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21135 pattern childGuard
    simpa only [d1261, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1261, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13402 pattern childGuard
    simpa only [d1261, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21137 (pattern : Twelve) (guard : d1 pattern = 1) : d1250 pattern ≤ (2 : Int) + d834 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1250, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13306 pattern childGuard
    simpa only [d1250, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1250, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21059 pattern childGuard
    simpa only [d1250, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21138 (pattern : Twelve) (guard : d1 pattern = 1) : d1255 pattern ≤ (2 : Int) + d849 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1255, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13294 pattern childGuard
    simpa only [d1255, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1255, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21137 pattern childGuard
    simpa only [d1255, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21139 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (2 : Int) + d835 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13306 pattern childGuard
    simpa only [d837, d835, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21062 pattern childGuard
    simpa only [d837, d835, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
