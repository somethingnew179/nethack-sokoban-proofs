/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons151
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c21280 (pattern : Twelve) (guard : d1 pattern = 1) : d75 pattern ≤ (2 : Int) + d138 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21276 pattern childGuard
    simpa only [d75, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21279 pattern childGuard
    simpa only [d75, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21281 (pattern : Twelve) (guard : d1 pattern = 1) : d92 pattern ≤ (2 : Int) + d145 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21274 pattern childGuard
    simpa only [d92, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21280 pattern childGuard
    simpa only [d92, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21282 (pattern : Twelve) (guard : d1 pattern = 1) : d102 pattern ≤ (2 : Int) + d149 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21268 pattern childGuard
    simpa only [d102, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21281 pattern childGuard
    simpa only [d102, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21283 (pattern : Twelve) (guard : d1 pattern = 1) : d76 pattern ≤ (2 : Int) + d136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d76, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21279 pattern childGuard
    simpa only [d76, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21284 (pattern : Twelve) (guard : d1 pattern = 1) : d93 pattern ≤ (2 : Int) + d144 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20285 pattern childGuard
    simpa only [d93, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21283 pattern childGuard
    simpa only [d93, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21285 (pattern : Twelve) (guard : d1 pattern = 1) : d57 pattern ≤ (2 : Int) + d130 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21271 pattern childGuard
    simpa only [d57, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21002 pattern childGuard
    simpa only [d57, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21286 (pattern : Twelve) (guard : d1 pattern = 1) : d77 pattern ≤ (2 : Int) + d139 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20309 pattern childGuard
    simpa only [d77, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21285 pattern childGuard
    simpa only [d77, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21287 (pattern : Twelve) (guard : d1 pattern = 1) : d78 pattern ≤ (2 : Int) + d138 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20309 pattern childGuard
    simpa only [d78, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21279 pattern childGuard
    simpa only [d78, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21288 (pattern : Twelve) (guard : d1 pattern = 1) : d94 pattern ≤ (2 : Int) + d146 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21286 pattern childGuard
    simpa only [d94, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21287 pattern childGuard
    simpa only [d94, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21289 (pattern : Twelve) (guard : d1 pattern = 1) : d103 pattern ≤ (2 : Int) + d150 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21284 pattern childGuard
    simpa only [d103, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21288 pattern childGuard
    simpa only [d103, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21290 (pattern : Twelve) (guard : d1 pattern = 1) : d110 pattern ≤ (2 : Int) + d153 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21282 pattern childGuard
    simpa only [d110, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21289 pattern childGuard
    simpa only [d110, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21291 (pattern : Twelve) (guard : d1 pattern = 1) : d37 pattern ≤ (2 : Int) + d122 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13488 pattern childGuard
    simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21292 (pattern : Twelve) (guard : d1 pattern = 1) : d58 pattern ≤ (2 : Int) + d131 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21271 pattern childGuard
    simpa only [d58, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21291 pattern childGuard
    simpa only [d58, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21293 (pattern : Twelve) (guard : d1 pattern = 1) : d79 pattern ≤ (2 : Int) + d140 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d79, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21292 pattern childGuard
    simpa only [d79, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21294 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (2 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d30, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13479 pattern childGuard
    simpa only [d30, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21295 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (2 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21294 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21296 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (2 : Int) + d141 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21295 pattern childGuard
    simpa only [d80, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21279 pattern childGuard
    simpa only [d80, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21297 (pattern : Twelve) (guard : d1 pattern = 1) : d95 pattern ≤ (2 : Int) + d147 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21293 pattern childGuard
    simpa only [d95, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21296 pattern childGuard
    simpa only [d95, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21298 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13514 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13516 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21299 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (2 : Int) + d124 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d38, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21298 pattern childGuard
    simpa only [d38, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21300 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (2 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13479 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13488 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21301 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (2 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13479 pattern childGuard
    simpa only [d23, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21300 pattern childGuard
    simpa only [d23, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21302 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (2 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21301 pattern childGuard
    simpa only [d40, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d40, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21303 (pattern : Twelve) (guard : d1 pattern = 1) : d60 pattern ≤ (2 : Int) + d133 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21299 pattern childGuard
    simpa only [d60, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21302 pattern childGuard
    simpa only [d60, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21304 (pattern : Twelve) (guard : d1 pattern = 1) : d81 pattern ≤ (2 : Int) + d142 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20326 pattern childGuard
    simpa only [d81, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21303 pattern childGuard
    simpa only [d81, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21305 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (2 : Int) + d126 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d38, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13514 pattern childGuard
    simpa only [d38, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21306 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (2 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13479 pattern childGuard
    simpa only [d39, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d39, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21307 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (2 : Int) + d134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21305 pattern childGuard
    simpa only [d59, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21306 pattern childGuard
    simpa only [d59, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21308 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (2 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13516 pattern childGuard
    simpa only [d24, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13591 pattern childGuard
    simpa only [d24, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21309 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (2 : Int) + d127 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13590 pattern childGuard
    simpa only [d41, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21308 pattern childGuard
    simpa only [d41, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21310 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (2 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13479 pattern childGuard
    simpa only [d16, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13514 pattern childGuard
    simpa only [d16, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21311 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (2 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13488 pattern childGuard
    simpa only [d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13575 pattern childGuard
    simpa only [d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21312 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (2 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21310 pattern childGuard
    simpa only [d25, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21311 pattern childGuard
    simpa only [d25, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21313 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (2 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21312 pattern childGuard
    simpa only [d42, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d42, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21314 (pattern : Twelve) (guard : d1 pattern = 1) : d61 pattern ≤ (2 : Int) + d135 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21309 pattern childGuard
    simpa only [d61, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21313 pattern childGuard
    simpa only [d61, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21315 (pattern : Twelve) (guard : d1 pattern = 1) : d82 pattern ≤ (2 : Int) + d143 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21307 pattern childGuard
    simpa only [d82, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21314 pattern childGuard
    simpa only [d82, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21316 (pattern : Twelve) (guard : d1 pattern = 1) : d96 pattern ≤ (2 : Int) + d148 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21304 pattern childGuard
    simpa only [d96, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21315 pattern childGuard
    simpa only [d96, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21317 (pattern : Twelve) (guard : d1 pattern = 1) : d104 pattern ≤ (2 : Int) + d151 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21297 pattern childGuard
    simpa only [d104, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21316 pattern childGuard
    simpa only [d104, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21318 (pattern : Twelve) (guard : d1 pattern = 1) : d105 pattern ≤ (2 : Int) + d152 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d105, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21288 pattern childGuard
    simpa only [d105, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d105, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d105, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21319 (pattern : Twelve) (guard : d1 pattern = 1) : d111 pattern ≤ (2 : Int) + d154 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d111, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21317 pattern childGuard
    simpa only [d111, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d111, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21318 pattern childGuard
    simpa only [d111, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21320 (pattern : Twelve) (guard : d1 pattern = 1) : d114 pattern ≤ (2 : Int) + d155 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d114, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21290 pattern childGuard
    simpa only [d114, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d114, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21319 pattern childGuard
    simpa only [d114, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21321 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (2 : Int) + d61 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20479 pattern childGuard
    simpa only [d55, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20355 pattern childGuard
    simpa only [d55, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21322 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (2 : Int) + d789 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20322 pattern childGuard
    simpa only [d80, d789, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21321 pattern childGuard
    simpa only [d80, d789, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21323 (pattern : Twelve) (guard : d1 pattern = 1) : d97 pattern ≤ (2 : Int) + d794 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20352 pattern childGuard
    simpa only [d97, d794, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21322 pattern childGuard
    simpa only [d97, d794, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21324 (pattern : Twelve) (guard : d1 pattern = 1) : d43 pattern ≤ (2 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d43, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13614 pattern childGuard
    simpa only [d43, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21325 (pattern : Twelve) (guard : d1 pattern = 1) : d62 pattern ≤ (2 : Int) + d69 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20322 pattern childGuard
    simpa only [d62, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21324 pattern childGuard
    simpa only [d62, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21326 (pattern : Twelve) (guard : d1 pattern = 1) : d83 pattern ≤ (2 : Int) + d790 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20362 pattern childGuard
    simpa only [d83, d790, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21325 pattern childGuard
    simpa only [d83, d790, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21327 (pattern : Twelve) (guard : d1 pattern = 1) : d44 pattern ≤ (2 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d44, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20408 pattern childGuard
    simpa only [d44, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21328 (pattern : Twelve) (guard : d1 pattern = 1) : d63 pattern ≤ (2 : Int) + d70 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20322 pattern childGuard
    simpa only [d63, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21327 pattern childGuard
    simpa only [d63, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21329 (pattern : Twelve) (guard : d1 pattern = 1) : d64 pattern ≤ (2 : Int) + d71 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20479 pattern childGuard
    simpa only [d64, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20571 pattern childGuard
    simpa only [d64, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21330 (pattern : Twelve) (guard : d1 pattern = 1) : d84 pattern ≤ (2 : Int) + d90 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21328 pattern childGuard
    simpa only [d84, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21329 pattern childGuard
    simpa only [d84, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21331 (pattern : Twelve) (guard : d1 pattern = 1) : d98 pattern ≤ (2 : Int) + d795 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21326 pattern childGuard
    simpa only [d98, d795, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21330 pattern childGuard
    simpa only [d98, d795, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21332 (pattern : Twelve) (guard : d1 pattern = 1) : d106 pattern ≤ (2 : Int) + d798 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21323 pattern childGuard
    simpa only [d106, d798, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21331 pattern childGuard
    simpa only [d106, d798, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21333 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (2 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d45, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d45, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21334 (pattern : Twelve) (guard : d1 pattern = 1) : d65 pattern ≤ (2 : Int) + d69 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20322 pattern childGuard
    simpa only [d65, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21333 pattern childGuard
    simpa only [d65, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21335 (pattern : Twelve) (guard : d1 pattern = 1) : d85 pattern ≤ (2 : Int) + d89 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20382 pattern childGuard
    simpa only [d85, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21334 pattern childGuard
    simpa only [d85, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21336 (pattern : Twelve) (guard : d1 pattern = 1) : d66 pattern ≤ (2 : Int) + d70 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20322 pattern childGuard
    simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20333 pattern childGuard
    simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21337 (pattern : Twelve) (guard : d1 pattern = 1) : d86 pattern ≤ (2 : Int) + d90 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21336 pattern childGuard
    simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21329 pattern childGuard
    simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21338 (pattern : Twelve) (guard : d1 pattern = 1) : d99 pattern ≤ (2 : Int) + d101 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21335 pattern childGuard
    simpa only [d99, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21337 pattern childGuard
    simpa only [d99, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21339 (pattern : Twelve) (guard : d1 pattern = 1) : d107 pattern ≤ (2 : Int) + d799 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21323 pattern childGuard
    simpa only [d107, d799, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21338 pattern childGuard
    simpa only [d107, d799, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21340 (pattern : Twelve) (guard : d1 pattern = 1) : d112 pattern ≤ (2 : Int) + d802 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d112, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21332 pattern childGuard
    simpa only [d112, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d112, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21339 pattern childGuard
    simpa only [d112, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21341 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (2 : Int) + d780 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d46, d780, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13491 pattern childGuard
    simpa only [d46, d780, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21342 (pattern : Twelve) (guard : d1 pattern = 1) : d67 pattern ≤ (2 : Int) + d784 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20322 pattern childGuard
    simpa only [d67, d784, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21341 pattern childGuard
    simpa only [d67, d784, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21343 (pattern : Twelve) (guard : d1 pattern = 1) : d87 pattern ≤ (2 : Int) + d791 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20322 pattern childGuard
    simpa only [d87, d791, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21342 pattern childGuard
    simpa only [d87, d791, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21344 (pattern : Twelve) (guard : d1 pattern = 1) : d68 pattern ≤ (2 : Int) + d70 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20322 pattern childGuard
    simpa only [d68, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20394 pattern childGuard
    simpa only [d68, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21345 (pattern : Twelve) (guard : d1 pattern = 1) : d88 pattern ≤ (2 : Int) + d90 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21344 pattern childGuard
    simpa only [d88, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21329 pattern childGuard
    simpa only [d88, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21346 (pattern : Twelve) (guard : d1 pattern = 1) : d100 pattern ≤ (2 : Int) + d796 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21343 pattern childGuard
    simpa only [d100, d796, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21345 pattern childGuard
    simpa only [d100, d796, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21347 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (2 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13491 pattern childGuard
    simpa only [d47, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d47, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21348 (pattern : Twelve) (guard : d1 pattern = 1) : d69 pattern ≤ (2 : Int) + d785 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20394 pattern childGuard
    simpa only [d69, d785, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21347 pattern childGuard
    simpa only [d69, d785, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21349 (pattern : Twelve) (guard : d1 pattern = 1) : d89 pattern ≤ (2 : Int) + d792 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20395 pattern childGuard
    simpa only [d89, d792, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21348 pattern childGuard
    simpa only [d89, d792, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21350 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13515 pattern childGuard
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21351 (pattern : Twelve) (guard : d1 pattern = 1) : d70 pattern ≤ (2 : Int) + d786 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20394 pattern childGuard
    simpa only [d70, d786, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21350 pattern childGuard
    simpa only [d70, d786, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21352 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13592 pattern childGuard
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21353 (pattern : Twelve) (guard : d1 pattern = 1) : d71 pattern ≤ (2 : Int) + d787 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20570 pattern childGuard
    simpa only [d71, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21352 pattern childGuard
    simpa only [d71, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21354 (pattern : Twelve) (guard : d1 pattern = 1) : d90 pattern ≤ (2 : Int) + d793 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21351 pattern childGuard
    simpa only [d90, d793, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21353 pattern childGuard
    simpa only [d90, d793, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21355 (pattern : Twelve) (guard : d1 pattern = 1) : d101 pattern ≤ (2 : Int) + d797 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21349 pattern childGuard
    simpa only [d101, d797, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21354 pattern childGuard
    simpa only [d101, d797, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21356 (pattern : Twelve) (guard : d1 pattern = 1) : d108 pattern ≤ (2 : Int) + d800 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21346 pattern childGuard
    simpa only [d108, d800, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21355 pattern childGuard
    simpa only [d108, d800, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21357 (pattern : Twelve) (guard : d1 pattern = 1) : d109 pattern ≤ (2 : Int) + d801 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d109, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21338 pattern childGuard
    simpa only [d109, d801, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d109, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d109, d801, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21358 (pattern : Twelve) (guard : d1 pattern = 1) : d113 pattern ≤ (2 : Int) + d803 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d113, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21356 pattern childGuard
    simpa only [d113, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d113, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21357 pattern childGuard
    simpa only [d113, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21359 (pattern : Twelve) (guard : d1 pattern = 1) : d115 pattern ≤ (2 : Int) + d804 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d115, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21340 pattern childGuard
    simpa only [d115, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d115, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21358 pattern childGuard
    simpa only [d115, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21360 (pattern : Twelve) (guard : d1 pattern = 1) : d116 pattern ≤ (2 : Int) + d805 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d116, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21320 pattern childGuard
    simpa only [d116, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d116, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21359 pattern childGuard
    simpa only [d116, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21361 (pattern : Twelve) (guard : d0 pattern = 1) : d805 pattern ≤ (2 : Int) + d805 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c21362 (pattern : Twelve) (guard : d1878 pattern = 1) : d806 pattern ≤ (2 : Int) + d805 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21360 pattern childGuard
    simpa only [d1878, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21361 pattern childGuard
    simpa only [d1878, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21363 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13320 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14008 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21364 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13320 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21363 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21365 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (2 : Int) + d874 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d27, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21364 pattern childGuard
    simpa only [d27, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21366 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (2 : Int) + d875 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13356 pattern childGuard
    simpa only [d816, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21364 pattern childGuard
    simpa only [d816, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21367 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (2 : Int) + d882 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21365 pattern childGuard
    simpa only [d824, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21366 pattern childGuard
    simpa only [d824, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21368 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (2 : Int) + d890 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d838, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21367 pattern childGuard
    simpa only [d838, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21369 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (2 : Int) + d876 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13418 pattern childGuard
    simpa only [d817, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20467 pattern childGuard
    simpa only [d817, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21370 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (2 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21369 pattern childGuard
    simpa only [d825, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21091 pattern childGuard
    simpa only [d825, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21371 (pattern : Twelve) (guard : d1 pattern = 1) : d839 pattern ≤ (2 : Int) + d891 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d839, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21370 pattern childGuard
    simpa only [d839, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21372 (pattern : Twelve) (guard : d1 pattern = 1) : d853 pattern ≤ (2 : Int) + d898 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21368 pattern childGuard
    simpa only [d853, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21371 pattern childGuard
    simpa only [d853, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21373 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (2 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21269 pattern childGuard
    simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20328 pattern childGuard
    simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21374 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (2 : Int) + d877 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d34, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21373 pattern childGuard
    simpa only [d34, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21375 (pattern : Twelve) (guard : d1 pattern = 1) : d826 pattern ≤ (2 : Int) + d884 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21374 pattern childGuard
    simpa only [d826, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21098 pattern childGuard
    simpa only [d826, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21376 (pattern : Twelve) (guard : d1 pattern = 1) : d840 pattern ≤ (2 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20309 pattern childGuard
    simpa only [d840, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21375 pattern childGuard
    simpa only [d840, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21377 (pattern : Twelve) (guard : d1 pattern = 1) : d841 pattern ≤ (2 : Int) + d893 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21101 pattern childGuard
    simpa only [d841, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21370 pattern childGuard
    simpa only [d841, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21378 (pattern : Twelve) (guard : d1 pattern = 1) : d854 pattern ≤ (2 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21376 pattern childGuard
    simpa only [d854, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21377 pattern childGuard
    simpa only [d854, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21379 (pattern : Twelve) (guard : d1 pattern = 1) : d861 pattern ≤ (2 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21372 pattern childGuard
    simpa only [d861, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21378 pattern childGuard
    simpa only [d861, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21380 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13488 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20472 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21381 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (2 : Int) + d878 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13356 pattern childGuard
    simpa only [d819, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21380 pattern childGuard
    simpa only [d819, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21382 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (2 : Int) + d885 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21374 pattern childGuard
    simpa only [d828, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21381 pattern childGuard
    simpa only [d828, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21383 (pattern : Twelve) (guard : d1 pattern = 1) : d842 pattern ≤ (2 : Int) + d894 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d842, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21382 pattern childGuard
    simpa only [d842, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21384 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (2 : Int) + d879 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d34, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21301 pattern childGuard
    simpa only [d34, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21385 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (2 : Int) + d886 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13328 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21384 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21386 (pattern : Twelve) (guard : d1 pattern = 1) : d843 pattern ≤ (2 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21385 pattern childGuard
    simpa only [d843, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21370 pattern childGuard
    simpa only [d843, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21387 (pattern : Twelve) (guard : d1 pattern = 1) : d855 pattern ≤ (2 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21383 pattern childGuard
    simpa only [d855, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21386 pattern childGuard
    simpa only [d855, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21388 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (2 : Int) + d873 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21300 pattern childGuard
    simpa only [d815, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20472 pattern childGuard
    simpa only [d815, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21389 (pattern : Twelve) (guard : d1 pattern = 1) : d820 pattern ≤ (2 : Int) + d880 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21388 pattern childGuard
    simpa only [d820, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d820, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21390 (pattern : Twelve) (guard : d1 pattern = 1) : d829 pattern ≤ (2 : Int) + d887 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21309 pattern childGuard
    simpa only [d829, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21389 pattern childGuard
    simpa only [d829, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21391 (pattern : Twelve) (guard : d1 pattern = 1) : d844 pattern ≤ (2 : Int) + d896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20326 pattern childGuard
    simpa only [d844, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21390 pattern childGuard
    simpa only [d844, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21392 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (2 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13514 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13575 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21393 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (2 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13514 pattern childGuard
    simpa only [d24, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21392 pattern childGuard
    simpa only [d24, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21394 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (2 : Int) + d881 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13590 pattern childGuard
    simpa only [d41, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21393 pattern childGuard
    simpa only [d41, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21395 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (2 : Int) + d888 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21394 pattern childGuard
    simpa only [d830, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21302 pattern childGuard
    simpa only [d830, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21396 (pattern : Twelve) (guard : d1 pattern = 1) : d831 pattern ≤ (2 : Int) + d889 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13615 pattern childGuard
    simpa only [d831, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20614 pattern childGuard
    simpa only [d831, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21397 (pattern : Twelve) (guard : d1 pattern = 1) : d845 pattern ≤ (2 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21395 pattern childGuard
    simpa only [d845, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21396 pattern childGuard
    simpa only [d845, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21398 (pattern : Twelve) (guard : d1 pattern = 1) : d856 pattern ≤ (2 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21391 pattern childGuard
    simpa only [d856, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21397 pattern childGuard
    simpa only [d856, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21399 (pattern : Twelve) (guard : d1 pattern = 1) : d862 pattern ≤ (2 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21387 pattern childGuard
    simpa only [d862, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21398 pattern childGuard
    simpa only [d862, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21400 (pattern : Twelve) (guard : d1 pattern = 1) : d863 pattern ≤ (2 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21378 pattern childGuard
    simpa only [d863, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d863, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21401 (pattern : Twelve) (guard : d1 pattern = 1) : d867 pattern ≤ (2 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21399 pattern childGuard
    simpa only [d867, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21400 pattern childGuard
    simpa only [d867, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21402 (pattern : Twelve) (guard : d1 pattern = 1) : d869 pattern ≤ (2 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21379 pattern childGuard
    simpa only [d869, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21401 pattern childGuard
    simpa only [d869, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21403 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (2 : Int) + d1247 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20458 pattern childGuard
    simpa only [d816, d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d816, d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21404 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (2 : Int) + d1249 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20350 pattern childGuard
    simpa only [d824, d1249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21403 pattern childGuard
    simpa only [d824, d1249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21405 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (2 : Int) + d1253 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d838, d1253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21404 pattern childGuard
    simpa only [d838, d1253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21406 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (2 : Int) + d1248 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13939 pattern childGuard
    simpa only [d823, d1248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d823, d1248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21407 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (2 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20556 pattern childGuard
    simpa only [d825, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20468 pattern childGuard
    simpa only [d825, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21408 (pattern : Twelve) (guard : d1 pattern = 1) : d846 pattern ≤ (2 : Int) + d1254 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21406 pattern childGuard
    simpa only [d846, d1254, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21407 pattern childGuard
    simpa only [d846, d1254, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21409 (pattern : Twelve) (guard : d1 pattern = 1) : d857 pattern ≤ (2 : Int) + d1258 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21405 pattern childGuard
    simpa only [d857, d1258, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21408 pattern childGuard
    simpa only [d857, d1258, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21410 (pattern : Twelve) (guard : d1 pattern = 1) : d832 pattern ≤ (2 : Int) + d836 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20479 pattern childGuard
    simpa only [d832, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21333 pattern childGuard
    simpa only [d832, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21411 (pattern : Twelve) (guard : d1 pattern = 1) : d847 pattern ≤ (2 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20382 pattern childGuard
    simpa only [d847, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21410 pattern childGuard
    simpa only [d847, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21412 (pattern : Twelve) (guard : d1 pattern = 1) : d833 pattern ≤ (2 : Int) + d837 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20479 pattern childGuard
    simpa only [d833, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20333 pattern childGuard
    simpa only [d833, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21413 (pattern : Twelve) (guard : d1 pattern = 1) : d848 pattern ≤ (2 : Int) + d852 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21412 pattern childGuard
    simpa only [d848, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21407 pattern childGuard
    simpa only [d848, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21414 (pattern : Twelve) (guard : d1 pattern = 1) : d858 pattern ≤ (2 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21411 pattern childGuard
    simpa only [d858, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21413 pattern childGuard
    simpa only [d858, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21415 (pattern : Twelve) (guard : d1 pattern = 1) : d864 pattern ≤ (2 : Int) + d1261 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21409 pattern childGuard
    simpa only [d864, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21414 pattern childGuard
    simpa only [d864, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21416 (pattern : Twelve) (guard : d1 pattern = 1) : d834 pattern ≤ (2 : Int) + d1250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20479 pattern childGuard
    simpa only [d834, d1250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21341 pattern childGuard
    simpa only [d834, d1250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21417 (pattern : Twelve) (guard : d1 pattern = 1) : d849 pattern ≤ (2 : Int) + d1255 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20322 pattern childGuard
    simpa only [d849, d1255, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21416 pattern childGuard
    simpa only [d849, d1255, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21418 (pattern : Twelve) (guard : d1 pattern = 1) : d835 pattern ≤ (2 : Int) + d837 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20479 pattern childGuard
    simpa only [d835, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20394 pattern childGuard
    simpa only [d835, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21419 (pattern : Twelve) (guard : d1 pattern = 1) : d850 pattern ≤ (2 : Int) + d852 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21418 pattern childGuard
    simpa only [d850, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21407 pattern childGuard
    simpa only [d850, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
