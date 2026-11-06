/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons121
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c17080 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d120 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1848, d36, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11068 pattern childGuard
    simpa only [d1848, d36, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17081 (pattern : Twelve) (guard : d1848 pattern = 1) : d378 pattern ≤ (1 : Int) + d129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d378, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17080 pattern childGuard
    simpa only [d378, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d378, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16987 pattern childGuard
    simpa only [d378, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17082 (pattern : Twelve) (guard : d1848 pattern = 1) : d394 pattern ≤ (1 : Int) + d136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11160 pattern childGuard
    simpa only [d394, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17081 pattern childGuard
    simpa only [d394, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17083 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (1 : Int) + d144 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17053 pattern childGuard
    simpa only [d407, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17082 pattern childGuard
    simpa only [d407, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17084 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (1 : Int) + d121 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d35, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11078 pattern childGuard
    simpa only [d1848, d35, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17085 (pattern : Twelve) (guard : d1848 pattern = 1) : d380 pattern ≤ (1 : Int) + d130 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17084 pattern childGuard
    simpa only [d380, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17019 pattern childGuard
    simpa only [d380, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17086 (pattern : Twelve) (guard : d1848 pattern = 1) : d399 pattern ≤ (1 : Int) + d137 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17060 pattern childGuard
    simpa only [d399, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17085 pattern childGuard
    simpa only [d399, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17087 (pattern : Twelve) (guard : d1848 pattern = 1) : d394 pattern ≤ (1 : Int) + d138 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17022 pattern childGuard
    simpa only [d394, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17081 pattern childGuard
    simpa only [d394, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17088 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (1 : Int) + d145 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17086 pattern childGuard
    simpa only [d407, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17087 pattern childGuard
    simpa only [d407, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17089 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (1 : Int) + d149 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17083 pattern childGuard
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17088 pattern childGuard
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17090 (pattern : Twelve) (guard : d1848 pattern = 1) : d399 pattern ≤ (1 : Int) + d139 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17022 pattern childGuard
    simpa only [d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17085 pattern childGuard
    simpa only [d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17091 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (1 : Int) + d146 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17090 pattern childGuard
    simpa only [d407, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17087 pattern childGuard
    simpa only [d407, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17092 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (1 : Int) + d150 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17083 pattern childGuard
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17091 pattern childGuard
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17093 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (1 : Int) + d153 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17089 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17092 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17094 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d122 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1848, d36, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11128 pattern childGuard
    simpa only [d1848, d36, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17095 (pattern : Twelve) (guard : d1848 pattern = 1) : d380 pattern ≤ (1 : Int) + d131 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17084 pattern childGuard
    simpa only [d380, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17094 pattern childGuard
    simpa only [d380, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17096 (pattern : Twelve) (guard : d1848 pattern = 1) : d399 pattern ≤ (1 : Int) + d140 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11106 pattern childGuard
    simpa only [d399, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17095 pattern childGuard
    simpa only [d399, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17097 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (1 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d35, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12318 pattern childGuard
    simpa only [d1848, d35, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17098 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (1 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11106 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17097 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17099 (pattern : Twelve) (guard : d1848 pattern = 1) : d394 pattern ≤ (1 : Int) + d141 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17098 pattern childGuard
    simpa only [d394, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17081 pattern childGuard
    simpa only [d394, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17100 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (1 : Int) + d147 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17096 pattern childGuard
    simpa only [d407, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17099 pattern childGuard
    simpa only [d407, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17101 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d118 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17102 (pattern : Twelve) (guard : d1848 pattern = 1) : d39 pattern ≤ (1 : Int) + d124 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d39, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d1848, d39, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d39, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17101 pattern childGuard
    simpa only [d1848, d39, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17103 (pattern : Twelve) (guard : d1848 pattern = 1) : d125 pattern ≤ (1 : Int) + d125 pattern := by
  omega
theorem c17104 (pattern : Twelve) (guard : d1848 pattern = 1) : d386 pattern ≤ (1 : Int) + d133 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d386, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17102 pattern childGuard
    simpa only [d386, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d386, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17103 pattern childGuard
    simpa only [d386, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17105 (pattern : Twelve) (guard : d1848 pattern = 1) : d400 pattern ≤ (1 : Int) + d142 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d400, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17037 pattern childGuard
    simpa only [d400, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d400, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17104 pattern childGuard
    simpa only [d400, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17106 (pattern : Twelve) (guard : d1848 pattern = 1) : d39 pattern ≤ (1 : Int) + d126 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d39, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d1848, d39, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d39, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16043 pattern childGuard
    simpa only [d1848, d39, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17107 (pattern : Twelve) (guard : d1848 pattern = 1) : d47 pattern ≤ (1 : Int) + d47 pattern := by
  omega
theorem c17108 (pattern : Twelve) (guard : d1848 pattern = 1) : d387 pattern ≤ (1 : Int) + d134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d387, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17106 pattern childGuard
    simpa only [d387, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d387, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17107 pattern childGuard
    simpa only [d387, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17109 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (1 : Int) + d127 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d40, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11132 pattern childGuard
    simpa only [d1848, d40, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d40, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11366 pattern childGuard
    simpa only [d1848, d40, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17110 (pattern : Twelve) (guard : d1848 pattern = 1) : d128 pattern ≤ (1 : Int) + d128 pattern := by
  omega
theorem c17111 (pattern : Twelve) (guard : d1848 pattern = 1) : d388 pattern ≤ (1 : Int) + d135 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d388, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17109 pattern childGuard
    simpa only [d388, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d388, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17110 pattern childGuard
    simpa only [d388, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17112 (pattern : Twelve) (guard : d1848 pattern = 1) : d401 pattern ≤ (1 : Int) + d143 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d401, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17108 pattern childGuard
    simpa only [d401, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d401, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17111 pattern childGuard
    simpa only [d401, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17113 (pattern : Twelve) (guard : d1848 pattern = 1) : d408 pattern ≤ (1 : Int) + d148 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d408, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17105 pattern childGuard
    simpa only [d408, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d408, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17112 pattern childGuard
    simpa only [d408, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17114 (pattern : Twelve) (guard : d1848 pattern = 1) : d414 pattern ≤ (1 : Int) + d151 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d414, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17100 pattern childGuard
    simpa only [d414, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d414, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17113 pattern childGuard
    simpa only [d414, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17115 (pattern : Twelve) (guard : d1848 pattern = 1) : d412 pattern ≤ (1 : Int) + d152 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d412, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17091 pattern childGuard
    simpa only [d412, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d412, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d412, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17116 (pattern : Twelve) (guard : d1848 pattern = 1) : d418 pattern ≤ (1 : Int) + d154 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d418, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17114 pattern childGuard
    simpa only [d418, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d418, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17115 pattern childGuard
    simpa only [d418, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17117 (pattern : Twelve) (guard : d1848 pattern = 1) : d421 pattern ≤ (1 : Int) + d155 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d421, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17093 pattern childGuard
    simpa only [d421, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d421, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17116 pattern childGuard
    simpa only [d421, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17118 (pattern : Twelve) (guard : d1848 pattern = 1) : d424 pattern ≤ (1 : Int) + d156 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d424, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17079 pattern childGuard
    simpa only [d424, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d424, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17117 pattern childGuard
    simpa only [d424, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17119 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (1 : Int) + d814 pattern := by
  omega
theorem c17120 (pattern : Twelve) (guard : d1848 pattern = 1) : d818 pattern ≤ (1 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d818, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17119 pattern childGuard
    simpa only [d1848, d818, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d818, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11094 pattern childGuard
    simpa only [d1848, d818, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17121 (pattern : Twelve) (guard : d1848 pattern = 1) : d1030 pattern ≤ (1 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1030, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11056 pattern childGuard
    simpa only [d1030, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1030, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17120 pattern childGuard
    simpa only [d1030, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17122 (pattern : Twelve) (guard : d1848 pattern = 1) : d1038 pattern ≤ (1 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1038, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16984 pattern childGuard
    simpa only [d1038, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1038, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17121 pattern childGuard
    simpa only [d1038, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17123 (pattern : Twelve) (guard : d1848 pattern = 1) : d366 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1848, d366, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11063 pattern childGuard
    simpa only [d1848, d366, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17124 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11099 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17125 (pattern : Twelve) (guard : d1848 pattern = 1) : d1031 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17123 pattern childGuard
    simpa only [d1031, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17124 pattern childGuard
    simpa only [d1031, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17126 (pattern : Twelve) (guard : d1848 pattern = 1) : d1032 pattern ≤ (1 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1032, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11069 pattern childGuard
    simpa only [d1032, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1032, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17041 pattern childGuard
    simpa only [d1032, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17127 (pattern : Twelve) (guard : d1848 pattern = 1) : d1039 pattern ≤ (1 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1039, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17125 pattern childGuard
    simpa only [d1039, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1039, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17126 pattern childGuard
    simpa only [d1039, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17128 (pattern : Twelve) (guard : d1848 pattern = 1) : d1048 pattern ≤ (1 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1048, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17122 pattern childGuard
    simpa only [d1048, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1048, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17127 pattern childGuard
    simpa only [d1048, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17129 (pattern : Twelve) (guard : d1848 pattern = 1) : d377 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d377, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11075 pattern childGuard
    simpa only [d377, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d377, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17017 pattern childGuard
    simpa only [d377, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17130 (pattern : Twelve) (guard : d1848 pattern = 1) : d818 pattern ≤ (1 : Int) + d818 pattern := by
  omega
theorem c17131 (pattern : Twelve) (guard : d1848 pattern = 1) : d1033 pattern ≤ (1 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11079 pattern childGuard
    simpa only [d1033, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17130 pattern childGuard
    simpa only [d1033, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17132 (pattern : Twelve) (guard : d1848 pattern = 1) : d1040 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1040, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17129 pattern childGuard
    simpa only [d1040, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1040, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17131 pattern childGuard
    simpa only [d1040, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17133 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11079 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17019 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17134 (pattern : Twelve) (guard : d1848 pattern = 1) : d1041 pattern ≤ (1 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17133 pattern childGuard
    simpa only [d1041, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17126 pattern childGuard
    simpa only [d1041, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17135 (pattern : Twelve) (guard : d1848 pattern = 1) : d1049 pattern ≤ (1 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1049, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17132 pattern childGuard
    simpa only [d1049, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1049, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17134 pattern childGuard
    simpa only [d1049, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17136 (pattern : Twelve) (guard : d1848 pattern = 1) : d1054 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1054, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17128 pattern childGuard
    simpa only [d1054, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1054, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17135 pattern childGuard
    simpa only [d1054, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17137 (pattern : Twelve) (guard : d1848 pattern = 1) : d1033 pattern ≤ (1 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11095 pattern childGuard
    simpa only [d1033, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17120 pattern childGuard
    simpa only [d1033, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17138 (pattern : Twelve) (guard : d1848 pattern = 1) : d1040 pattern ≤ (1 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1040, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17012 pattern childGuard
    simpa only [d1040, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1040, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17137 pattern childGuard
    simpa only [d1040, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17139 (pattern : Twelve) (guard : d1848 pattern = 1) : d1041 pattern ≤ (1 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17124 pattern childGuard
    simpa only [d1041, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17126 pattern childGuard
    simpa only [d1041, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17140 (pattern : Twelve) (guard : d1848 pattern = 1) : d1049 pattern ≤ (1 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1049, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17138 pattern childGuard
    simpa only [d1049, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1049, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17139 pattern childGuard
    simpa only [d1049, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17141 (pattern : Twelve) (guard : d1848 pattern = 1) : d1042 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17022 pattern childGuard
    simpa only [d1042, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17131 pattern childGuard
    simpa only [d1042, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17142 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (1 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17141 pattern childGuard
    simpa only [d1050, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17134 pattern childGuard
    simpa only [d1050, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17143 (pattern : Twelve) (guard : d1848 pattern = 1) : d1055 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1055, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17140 pattern childGuard
    simpa only [d1055, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1055, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17142 pattern childGuard
    simpa only [d1055, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17144 (pattern : Twelve) (guard : d1848 pattern = 1) : d1060 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17136 pattern childGuard
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17143 pattern childGuard
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17145 (pattern : Twelve) (guard : d1848 pattern = 1) : d818 pattern ≤ (1 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d818, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17119 pattern childGuard
    simpa only [d1848, d818, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d818, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12318 pattern childGuard
    simpa only [d1848, d818, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17146 (pattern : Twelve) (guard : d1848 pattern = 1) : d1033 pattern ≤ (1 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11079 pattern childGuard
    simpa only [d1033, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17145 pattern childGuard
    simpa only [d1033, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17147 (pattern : Twelve) (guard : d1848 pattern = 1) : d1043 pattern ≤ (1 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1043, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17033 pattern childGuard
    simpa only [d1043, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1043, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17146 pattern childGuard
    simpa only [d1043, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17148 (pattern : Twelve) (guard : d1848 pattern = 1) : d1041 pattern ≤ (1 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11079 pattern childGuard
    simpa only [d1041, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17126 pattern childGuard
    simpa only [d1041, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17149 (pattern : Twelve) (guard : d1848 pattern = 1) : d1051 pattern ≤ (1 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1051, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17147 pattern childGuard
    simpa only [d1051, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1051, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17148 pattern childGuard
    simpa only [d1051, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17150 (pattern : Twelve) (guard : d1848 pattern = 1) : d820 pattern ≤ (1 : Int) + d820 pattern := by
  omega
theorem c17151 (pattern : Twelve) (guard : d1848 pattern = 1) : d1034 pattern ≤ (1 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1034, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11134 pattern childGuard
    simpa only [d1034, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1034, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17150 pattern childGuard
    simpa only [d1034, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17152 (pattern : Twelve) (guard : d1848 pattern = 1) : d1044 pattern ≤ (1 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1044, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17037 pattern childGuard
    simpa only [d1044, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1044, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17151 pattern childGuard
    simpa only [d1044, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17153 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (1 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11134 pattern childGuard
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17038 pattern childGuard
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17154 (pattern : Twelve) (guard : d1848 pattern = 1) : d822 pattern ≤ (1 : Int) + d822 pattern := by
  omega
theorem c17155 (pattern : Twelve) (guard : d1848 pattern = 1) : d1035 pattern ≤ (1 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1035, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11145 pattern childGuard
    simpa only [d1035, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1035, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17154 pattern childGuard
    simpa only [d1035, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17156 (pattern : Twelve) (guard : d1848 pattern = 1) : d1045 pattern ≤ (1 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1045, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17153 pattern childGuard
    simpa only [d1045, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1045, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17155 pattern childGuard
    simpa only [d1045, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17157 (pattern : Twelve) (guard : d1848 pattern = 1) : d1052 pattern ≤ (1 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1052, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17152 pattern childGuard
    simpa only [d1052, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1052, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17156 pattern childGuard
    simpa only [d1052, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17158 (pattern : Twelve) (guard : d1848 pattern = 1) : d1056 pattern ≤ (1 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1056, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17149 pattern childGuard
    simpa only [d1056, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1056, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17157 pattern childGuard
    simpa only [d1056, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17159 (pattern : Twelve) (guard : d1848 pattern = 1) : d1057 pattern ≤ (1 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1057, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17142 pattern childGuard
    simpa only [d1057, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1057, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d1057, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17160 (pattern : Twelve) (guard : d1848 pattern = 1) : d1061 pattern ≤ (1 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1061, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17158 pattern childGuard
    simpa only [d1061, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1061, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17159 pattern childGuard
    simpa only [d1061, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17161 (pattern : Twelve) (guard : d1848 pattern = 1) : d1064 pattern ≤ (1 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1064, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17144 pattern childGuard
    simpa only [d1064, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1064, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17160 pattern childGuard
    simpa only [d1064, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17162 (pattern : Twelve) (guard : d1848 pattern = 1) : d1042 pattern ≤ (1 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11160 pattern childGuard
    simpa only [d1042, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17137 pattern childGuard
    simpa only [d1042, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17163 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (1 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17162 pattern childGuard
    simpa only [d1050, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17139 pattern childGuard
    simpa only [d1050, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17164 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17163 pattern childGuard
    simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17142 pattern childGuard
    simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17165 (pattern : Twelve) (guard : d1848 pattern = 1) : d1042 pattern ≤ (1 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11106 pattern childGuard
    simpa only [d1042, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17146 pattern childGuard
    simpa only [d1042, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17166 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (1 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17165 pattern childGuard
    simpa only [d1050, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17148 pattern childGuard
    simpa only [d1050, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17167 (pattern : Twelve) (guard : d1848 pattern = 1) : d1058 pattern ≤ (1 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1058, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17166 pattern childGuard
    simpa only [d1058, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1058, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17157 pattern childGuard
    simpa only [d1058, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17168 (pattern : Twelve) (guard : d1848 pattern = 1) : d1062 pattern ≤ (1 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1062, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17167 pattern childGuard
    simpa only [d1062, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1062, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17159 pattern childGuard
    simpa only [d1062, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17169 (pattern : Twelve) (guard : d1848 pattern = 1) : d1065 pattern ≤ (1 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1065, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17164 pattern childGuard
    simpa only [d1065, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1065, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17168 pattern childGuard
    simpa only [d1065, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17170 (pattern : Twelve) (guard : d1848 pattern = 1) : d1067 pattern ≤ (1 : Int) + d869 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17161 pattern childGuard
    simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17169 pattern childGuard
    simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17171 (pattern : Twelve) (guard : d1848 pattern = 1) : d1068 pattern ≤ (1 : Int) + d869 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17170 pattern childGuard
    simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17169 pattern childGuard
    simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17172 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d874 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1848, d36, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11216 pattern childGuard
    simpa only [d1848, d36, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17173 (pattern : Twelve) (guard : d1848 pattern = 1) : d818 pattern ≤ (1 : Int) + d875 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d818, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17119 pattern childGuard
    simpa only [d1848, d818, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d818, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11216 pattern childGuard
    simpa only [d1848, d818, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17174 (pattern : Twelve) (guard : d1848 pattern = 1) : d1033 pattern ≤ (1 : Int) + d882 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17172 pattern childGuard
    simpa only [d1033, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17173 pattern childGuard
    simpa only [d1033, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17175 (pattern : Twelve) (guard : d1848 pattern = 1) : d1042 pattern ≤ (1 : Int) + d890 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11160 pattern childGuard
    simpa only [d1042, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17174 pattern childGuard
    simpa only [d1042, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17176 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (1 : Int) + d876 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11067 pattern childGuard
    simpa only [d1848, d29, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11144 pattern childGuard
    simpa only [d1848, d29, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17177 (pattern : Twelve) (guard : d1848 pattern = 1) : d1032 pattern ≤ (1 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1032, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17176 pattern childGuard
    simpa only [d1032, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1032, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17041 pattern childGuard
    simpa only [d1032, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17178 (pattern : Twelve) (guard : d1848 pattern = 1) : d1041 pattern ≤ (1 : Int) + d891 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17124 pattern childGuard
    simpa only [d1041, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17177 pattern childGuard
    simpa only [d1041, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17179 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (1 : Int) + d898 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17175 pattern childGuard
    simpa only [d1050, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17178 pattern childGuard
    simpa only [d1050, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17180 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17181 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d877 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1848, d36, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17180 pattern childGuard
    simpa only [d1848, d36, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17182 (pattern : Twelve) (guard : d1848 pattern = 1) : d1033 pattern ≤ (1 : Int) + d884 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17181 pattern childGuard
    simpa only [d1033, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17130 pattern childGuard
    simpa only [d1033, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17183 (pattern : Twelve) (guard : d1848 pattern = 1) : d1042 pattern ≤ (1 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17022 pattern childGuard
    simpa only [d1042, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17182 pattern childGuard
    simpa only [d1042, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17184 (pattern : Twelve) (guard : d1848 pattern = 1) : d1041 pattern ≤ (1 : Int) + d893 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17133 pattern childGuard
    simpa only [d1041, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17177 pattern childGuard
    simpa only [d1041, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17185 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (1 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17183 pattern childGuard
    simpa only [d1050, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17184 pattern childGuard
    simpa only [d1050, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17186 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (1 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17179 pattern childGuard
    simpa only [d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17185 pattern childGuard
    simpa only [d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17187 (pattern : Twelve) (guard : d1848 pattern = 1) : d818 pattern ≤ (1 : Int) + d878 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d818, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17119 pattern childGuard
    simpa only [d1848, d818, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d818, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11133 pattern childGuard
    simpa only [d1848, d818, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17188 (pattern : Twelve) (guard : d1848 pattern = 1) : d1033 pattern ≤ (1 : Int) + d885 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17181 pattern childGuard
    simpa only [d1033, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17187 pattern childGuard
    simpa only [d1033, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17189 (pattern : Twelve) (guard : d1848 pattern = 1) : d1042 pattern ≤ (1 : Int) + d894 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11106 pattern childGuard
    simpa only [d1042, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17188 pattern childGuard
    simpa only [d1042, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17190 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d119 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17191 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d879 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1848, d36, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17190 pattern childGuard
    simpa only [d1848, d36, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17192 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d886 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11079 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17191 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17193 (pattern : Twelve) (guard : d1848 pattern = 1) : d1041 pattern ≤ (1 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17192 pattern childGuard
    simpa only [d1041, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17177 pattern childGuard
    simpa only [d1041, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17194 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (1 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17189 pattern childGuard
    simpa only [d1050, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17193 pattern childGuard
    simpa only [d1050, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17195 (pattern : Twelve) (guard : d1848 pattern = 1) : d880 pattern ≤ (1 : Int) + d880 pattern := by
  omega
theorem c17196 (pattern : Twelve) (guard : d1848 pattern = 1) : d1036 pattern ≤ (1 : Int) + d887 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1036, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17109 pattern childGuard
    simpa only [d1036, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1036, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17195 pattern childGuard
    simpa only [d1036, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17197 (pattern : Twelve) (guard : d1848 pattern = 1) : d1046 pattern ≤ (1 : Int) + d896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1046, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17037 pattern childGuard
    simpa only [d1046, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1046, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17196 pattern childGuard
    simpa only [d1046, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17198 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (1 : Int) + d881 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d40, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11132 pattern childGuard
    simpa only [d1848, d40, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d40, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17101 pattern childGuard
    simpa only [d1848, d40, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17199 (pattern : Twelve) (guard : d1848 pattern = 1) : d1037 pattern ≤ (1 : Int) + d888 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1037, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17198 pattern childGuard
    simpa only [d1037, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1037, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17103 pattern childGuard
    simpa only [d1037, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17200 (pattern : Twelve) (guard : d1848 pattern = 1) : d889 pattern ≤ (1 : Int) + d889 pattern := by
  omega
theorem c17201 (pattern : Twelve) (guard : d1848 pattern = 1) : d1047 pattern ≤ (1 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1047, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17199 pattern childGuard
    simpa only [d1047, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1047, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17200 pattern childGuard
    simpa only [d1047, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17202 (pattern : Twelve) (guard : d1848 pattern = 1) : d1053 pattern ≤ (1 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1053, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17197 pattern childGuard
    simpa only [d1053, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1053, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17201 pattern childGuard
    simpa only [d1053, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17203 (pattern : Twelve) (guard : d1848 pattern = 1) : d1059 pattern ≤ (1 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1059, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17194 pattern childGuard
    simpa only [d1059, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1059, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17202 pattern childGuard
    simpa only [d1059, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17204 (pattern : Twelve) (guard : d1848 pattern = 1) : d1057 pattern ≤ (1 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1057, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17185 pattern childGuard
    simpa only [d1057, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1057, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d1057, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17205 (pattern : Twelve) (guard : d1848 pattern = 1) : d1063 pattern ≤ (1 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1063, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17203 pattern childGuard
    simpa only [d1063, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1063, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17204 pattern childGuard
    simpa only [d1063, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17206 (pattern : Twelve) (guard : d1848 pattern = 1) : d1066 pattern ≤ (1 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1066, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17186 pattern childGuard
    simpa only [d1066, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1066, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17205 pattern childGuard
    simpa only [d1066, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17207 (pattern : Twelve) (guard : d1848 pattern = 1) : d1069 pattern ≤ (1 : Int) + d907 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1069, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17171 pattern childGuard
    simpa only [d1069, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1069, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17206 pattern childGuard
    simpa only [d1069, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17208 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (1 : Int) + d1275 pattern := by
  omega
theorem c17209 (pattern : Twelve) (guard : d1848 pattern = 1) : d1444 pattern ≤ (1 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1444, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17208 pattern childGuard
    simpa only [d1848, d1444, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1444, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11216 pattern childGuard
    simpa only [d1848, d1444, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17210 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (1 : Int) + d872 pattern := by
  omega
theorem c17211 (pattern : Twelve) (guard : d1848 pattern = 1) : d1280 pattern ≤ (1 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17210 pattern childGuard
    simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11216 pattern childGuard
    simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17212 (pattern : Twelve) (guard : d1848 pattern = 1) : d1445 pattern ≤ (1 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17209 pattern childGuard
    simpa only [d1445, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17211 pattern childGuard
    simpa only [d1445, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17213 (pattern : Twelve) (guard : d1848 pattern = 1) : d1448 pattern ≤ (1 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1448, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17125 pattern childGuard
    simpa only [d1448, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1448, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17212 pattern childGuard
    simpa only [d1448, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17214 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11067 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11226 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17215 (pattern : Twelve) (guard : d1848 pattern = 1) : d1449 pattern ≤ (1 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17214 pattern childGuard
    simpa only [d1449, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d1449, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17216 (pattern : Twelve) (guard : d1848 pattern = 1) : d1455 pattern ≤ (1 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1455, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17213 pattern childGuard
    simpa only [d1455, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1455, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17215 pattern childGuard
    simpa only [d1455, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17217 (pattern : Twelve) (guard : d1848 pattern = 1) : d1444 pattern ≤ (1 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1444, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17208 pattern childGuard
    simpa only [d1848, d1444, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1444, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11243 pattern childGuard
    simpa only [d1848, d1444, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17218 (pattern : Twelve) (guard : d1848 pattern = 1) : d1280 pattern ≤ (1 : Int) + d1280 pattern := by
  omega
theorem c17219 (pattern : Twelve) (guard : d1848 pattern = 1) : d1445 pattern ≤ (1 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17217 pattern childGuard
    simpa only [d1445, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17218 pattern childGuard
    simpa only [d1445, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
